open memory_model_js as js
open memory_model_aarch64 as aarch64

pred compilation_mapping[EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // two events cannot be mapped to a single event
  map[Natural] in EX.EV lone -> EX_t.EV

  // target events cannot be invented by the mapping
  all e : EX_t.EV | one e.~(map[Natural])

  // source events cannot be discarded by the mapping
  all e : EX.EV | some map[Natural,e]

  // the initial write is unaltered
  (EX.IW) = (EX_t.IW)

  // SC reads become strong acquire reads
  all e : EX.((R - W) & SC) {
    all loc:Natural | loc in e.reads => map[loc,e] = e else no map[loc,e]
    e in EX_t.A
  }

  // SC writes become release writes
  all e : EX.((W - R) & SC) {
    all loc:Natural | loc in e.writes => map[loc,e] = e else no map[loc,e]
    e in EX_t.L
  }

  // Tearfree non-atomic reads become bare reads
  all e : EX.(R & Unord & Tearfree) {
    all loc:Natural | loc in e.reads => map[loc,e] = e else no map[loc,e]
    e in EX_t.(R - Q)
  }

  // Tearfree non-atomic writes become bare writes
  all e : EX.(W & Unord & Tearfree) {
    all loc:Natural | loc in e.writes => map[loc,e] = e else no map[loc,e]
    e in EX_t.(W - L)
  }

  // Tearing non-atomic reads are split byte-wise
  all e : EX.((R & Unord) - Tearfree), loc:Natural {
    loc in e.reads => ((one map[loc,e]) && (map[loc,e].reads = loc) && map[loc,e] in EX_t.(R - Q)) else no map[loc,e]
  }

  // Tearing non-atomic writes are split byte-wise
  all e : EX.((W & Unord) - Tearfree), loc:Natural {
    loc in e.writes => ((one map[loc,e]) && (map[loc,e].writes = loc) && map[loc,e] in EX_t.(W - L)) else no map[loc,e]
  }

  // SC rmws become a pair of atomic-ordered A load and L store
  all e : EX.(R & W & SC) {
    let e_R = ((map[Natural,e]) & (EX_t.R)) {
      one e_R
      e_R.reads = e.reads
      e_R in (EX_t.A)

    let e_W = ((map[Natural,e]) & (EX_t.W)) {
      one e_W
      e_W.writes = e.writes
      e_W in (EX_t.L)

    all loc:Natural {
    loc in e.reads => (
      (map[loc,e]) = (e_R + e_W)
    ) else no map[loc,e]
    }}}
  }

  // the rmw relation captures pair-mapped rmws from the JS source
  EX_t.rmw = EX_t.A <: ((~(map[Natural])) . (map[Natural])) :> EX_t.L

  // the mapping preserves sb
  EX_t.sb = (~(map[Natural]) . (EX.sb) . (map[Natural])) + EX_t.rmw
  
  // the mapping preserves threads
  (EX_t.sthd) = ~(map[Natural]) . (EX.sthd) . (map[Natural])

  // the mapping preserves rfb
  all loc:Natural | EX.rfb[loc] = map[loc] . (EX_t.rfb[loc]) . ~(map[loc])

}

// note that the below two conditions should be exclusive with the dead condition
// define a construction of a JS tot relation from a corresponding AArch64 execution
// always succeeds, making this "proof technique" sound
pred mapping_tot[EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // include program order in tot
  EX.sb in EX.tot

  // the mapping preserves tot/ob for SC/L/A accesses
  // invariant: all SC/L/A mappings are aligned to aligned, and non-rmw events are one-to-one
  (map[Natural]) . (((EX_t.(L+A) <: (^(EX_t.ob)) :> EX_t.(L+A))) - EX_t.rmw) . (~(map[Natural]))
    in EX.tot
}

// an alternative characterisation of deadness appropriate for the fixed JS model
pred compilation_mapping_tot[EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {
  compilation_mapping[EX, EX_t, map]

  // the mapping preserves tot/ob for SC/L/A accesses
  // invariant: all SC/L/A mappings are one-to-one (aligned to aligned)
  mapping_tot[EX, EX_t, map]
}

pred hard_dead [EX:ExecJS] {
  
  // not interested in violations that are only wrong in the construction of the JS execution
  EX.hb in EX.tot

  // all W to R_sc edges must be justified by hb
  all loc:Natural | ((evs_loc[EX.W, loc]) <: EX.tot :> (evs_loc[EX.(R & SC), loc])) in EX.hb

  // all W_sc to W edges must be justified by hb
  all loc:Natural | ((evs_loc[EX.(W & SC), loc]) <: EX.tot :> (evs_loc[EX.W, loc])) in EX.hb
}

pred dead [EX:ExecJS] {

  // not interested in violations that are only wrong in the construction of the JS execution
  EX.hb in EX.tot

  // all W to R_sc edges must be justified by hb
  all loc:Natural | ((evs_loc[EX.W, loc]) <: EX.tot :> (evs_loc[EX.(R & SC), loc])) in EX.hb

  // all W_sc to W' edges must be justified either by hb or by a single indirection through a fixed tot shape
  // indirection: W_sc < R_b and W_c < W' and W_a sw R_b << W_c and W_a < W_c
  // this approach is freakishly inefficient - write relationally
  all loc:Natural, W_sc : EX.(W & SC), W' : EX.W |
    (loc in (W_sc.writes & W'.writes) && (W_sc -> W') in EX.tot) =>
      ( (W_sc -> W') in EX.hb ||
        (some W_a:EX.W, R_b:EX.sw[W_a], W_c:(EX.tot[R_b] & EX.SC & EX.hb[W_a]) | 
          R_b.reads = W_c.writes && (W_sc -> R_b) in EX.hb && (W_c -> W') in EX.hb
        )
      )
}

pred find_stephen[EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // Every event must be aligned
  all X:EX.(R+W) | aligned_one[X] || aligned_two[X] || aligned_four[X] || aligned_eight[X]

  no EX.IW

  // No rmws in JS
  no EX.(W & R)

  EX.sthd in *(EX.sb) + ~*(EX.sb)
  EX_t.sthd in *(EX_t.sb) + ~*(EX_t.sb)

  // some (EX.EV - EX.Tearfree)

  not (consistent_stephen_unfixed[EX])
  
  (consistent[EX_t])

  dead[EX]

  // We have a valid application of the mapping
  compilation_mapping[EX, EX_t, map]

}


pred check_compilation [EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  no EX.IW

  // EX_t.sthd in *(EX_t.sb) + ~*(EX_t.sb)

  // some (EX.EV - EX.Tearfree)

  not (consistent[EX])
  
  (consistent[EX_t])

  // dead[EX]

  // We have a valid application of the mapping
  compilation_mapping_tot[EX, EX_t, map]

}

pred check_compilation_aligned_no_rmw [EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // Every event must be aligned
  all X:EX.(R+W) | aligned_one[X] || aligned_two[X] || aligned_four[X] || aligned_eight[X]

  no EX.(R&W)
  check_compilation[EX, EX_t, map]
}

pred check_compilation_aligned_some_rmw [EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // Every event must be aligned
  all X:EX.(R+W) | aligned_one[X] || aligned_two[X] || aligned_four[X] || aligned_eight[X]

  some EX.(R&W)
  check_compilation[EX, EX_t, map]
}

pred check_compilation_unaligned_no_rmw [EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // Some event is un-aligned
  some (EX.EV - EX.Tearfree)

  no EX.(R&W)
  check_compilation[EX, EX_t, map]
}

pred check_compilation_unaligned_some_rmw [EX:ExecJS, EX_t:ExecAArch64, map:Natural->EX.EV->EX_t.EV] {

  // Some event is un-aligned
  some (EX.EV - EX.Tearfree)

  some EX.(R&W)
  check_compilation[EX, EX_t, map]
}

// run check_compilation for exactly 2 Exec, 6 E, 3 Natural
// run check_compilation_aligned_no_rmw for exactly 2 Exec, 6 E, 3 Natural
// run check_compilation_aligned_some_rmw for exactly 2 Exec, 6 E, 3 Natural
// run check_compilation_unaligned_no_rmw for exactly 2 Exec, 6 E, 3 Natural
// run check_compilation_unaligned_some_rmw for exactly 2 Exec, 6 E, 3 Natural
// run find_stephen for exactly 2 Exec, 6 E, 2 Natural
