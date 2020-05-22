open memory_model_base as memory

sig ExecJS extends Exec {
  sw : EV -> EV, // synchronizes-with
  hb : EV -> EV, // happens-before
  tot : EV -> EV, // total-order

  // consistency modes
  SC : set EV,
  Unord : set EV,
  Init : set EV,

  // tearing
  Tearfree : set EV
    
}{
  // every event reads or writes
  EV = W + R

  // consistency modes are exclusive
  disj[SC, Unord, Init]

  // every event has a consistency mode
  EV = SC + Unord + Init

  // RMW events are all SC
  (R&W) in SC

  // only the initial write is Init
  Init = IW

  // sequenced-before is an intra-thread total order
  sthd in *(sb) + ~*(sb)

  // JavaScript has no 8-byte events (yet - BigInt)
  no X:((R+W)-IW) | (size_eight[X])

  // Every SC event must be aligned
  all X:SC | (aligned_one[X] || aligned_two[X] || aligned_four[X]) // || aligned_eight[X])

  // non-aligned events are tearing
  Tearfree = { X:EV | (aligned_one[X] || aligned_two[X] || aligned_four[X]) || X in Init }

  // two same-range SC events synchronize
  // reading purely from Init also synchronizes
  sw = {Y:W, X:R | (X->Y) in rf && X in SC && ( (Y in SC && X.reads = Y.writes) || (Y in Init && rf[X] = Y) )}

  // happens-before is the transitive closure of sequenced-before and synchronizes-with
  // plus the IW happens-before all other events
  hb = ^((sb+sw) + (IW->(EV - IW)) )

  // happens-before is a strict partial order
  // strict_partial_order[hb]

  // total-order is a strict total order
  strict_total_order[tot, EV]
}

pred consistent[EX:ExecJS]{

  // happens-before is a subset of total-order
  hb in tot

  // no-tear rule
  all X:EX.Tearfree | lone { Y:EX.rf[X] | Y in EX.Tearfree && X.reads = Y.writes }

  // reads-from must be hb-consistent
  all X:EX.R, Y:EX.rf[X] | !( (X->Y) in EX.hb )

  all X:EX.R, loc:X.reads, Y:EX.rfb[loc,X] | no Z:EX.W | (Y->Z) in EX.hb && (Z->X) in EX.hb && loc in Z.writes

  // SC events must respect total-order
  all Y:EX.W, X:EX.sw[Y] | no Z:(EX.W & EX.SC) | (Y->Z) in EX.tot && (Z->X) in EX.tot && Z.writes = X.reads

  // dagger and ddagger
  all X:EX.R, Y:EX.rf[X] | ((Y->X) in EX.hb && Y in EX.SC) => (no Z:(EX.W & EX.SC) | (Y->Z) in EX.tot && (Z->X) in EX.hb && Z.writes = Y.writes)
  all X:EX.R, Y:EX.rf[X] | ((Y->X) in EX.hb && X in EX.SC) => (no Z:(EX.W & EX.SC) | (Y->Z) in EX.hb && (Z->X) in EX.tot && Z.writes = X.reads)
}

pred consistent_stephen_unfixed[EX:ExecJS]{

  // no-tear rule
  all X:EX.Tearfree | lone { Y:EX.rf[X] | Y in EX.Tearfree && X.reads = Y.writes }

  // reads-from must be hb-consistent
  all X:EX.R, Y:EX.rf[X] | !( (X->Y) in EX.hb )

  all X:EX.R, loc:X.reads, Y:EX.rfb[loc,X] | no Z:EX.W | (Y->Z) in EX.hb && (Z->X) in EX.hb && loc in Z.writes

  // unfixed: events must respect total-order
  all Y:EX.W, X:EX.sw[Y] | no Z:(EX.W) | (Y->Z) in EX.tot && (Z->X) in EX.tot && Z.writes = X.reads

  // dagger and ddagger
  all X:EX.R, Y:EX.rf[X] | ((Y->X) in EX.hb && Y in EX.SC) => (no Z:(EX.W & EX.SC) | (Y->Z) in EX.tot && (Z->X) in EX.hb && Z.writes = Y.writes)
  all X:EX.R, Y:EX.rf[X] | ((Y->X) in EX.hb && X in EX.SC) => (no Z:(EX.W & EX.SC) | (Y->Z) in EX.hb && (Z->X) in EX.tot && Z.writes = X.reads)
}

pred consistent_sc_unfixed[EX:ExecJS]{

  // no-tear rule
  all X:EX.Tearfree | lone { Y:EX.rf[X] | Y in EX.Tearfree && X.reads = Y.writes }

  // reads-from must be hb-consistent
  all X:EX.R, Y:EX.rf[X] | !( (X->Y) in EX.hb )

  all X:EX.R, loc:X.reads, Y:EX.rfb[loc,X] | no Z:EX.W | (Y->Z) in EX.hb && (Z->X) in EX.hb && loc in Z.writes

  // SC events must respect total-order
  all Y:EX.W, X:EX.sw[Y] | no Z:(EX.W & EX.SC) | (Y->Z) in EX.tot && (Z->X) in EX.tot && Z.writes = X.reads
}

// ----------------------------------------------------------------------

pred split_tearfree_execs[EX:ExecJS, EX_s:ExecJS, map:Natural->EX.EV->EX_s.EV] {
  
  // two events cannot be mapped to a single event
  map[Natural] in EX.EV lone -> EX_s.EV

  // target events cannot be invented by the mapping
  all e : EX_s.EV | one e.~(map[Natural])

  // source events cannot be discarded by the mapping
  all e : EX.EV | some map[Natural,e]

  // the initial write is unaltered
  (EX.IW) = (EX_s.IW)

  // SC reads are unaltered
  all e : EX.(R & SC) {
    all loc:Natural | loc in e.reads => map[loc,e] = e else no map[loc,e]
    e in EX_s.(R & SC)
  }

  // SC writes are unaltered
  all e : EX.(W & SC) {
    all loc:Natural | loc in e.writes => map[loc,e] = e else no map[loc,e]
    e in EX_s.(W & SC)
  }

  // Tearfree non-atomic reads are unaltered
  all e : EX.(R & Unord & Tearfree) {
    all loc:Natural | loc in e.reads => map[loc,e] = e else no map[loc,e]
    e in EX_s.(R & Unord & Tearfree)
  }

  // Tearfree non-atomic writes are unaltered
  all e : EX.(W & Unord & Tearfree) {
    all loc:Natural | loc in e.writes => map[loc,e] = e else no map[loc,e]
    e in EX_s.(W & Unord & Tearfree)
  }

  // Tearing non-atomic reads are split byte-wise
  all e : EX.((R & Unord) - Tearfree), loc:Natural {
    loc in e.reads => ((one map[loc,e]) && (map[loc,e].reads = loc) && map[loc,e] in EX_s.(R & Unord)) else no map[loc,e]
  }

  // Tearing non-atomic writes are split byte-wise
  all e : EX.((W & Unord) - Tearfree), loc:Natural {
    loc in e.writes => ((one map[loc,e]) && (map[loc,e].writes = loc) && map[loc,e] in EX_s.(W & Unord)) else no map[loc,e]
  }

  // the mapping preserves sb
  EX_s.sb = ~(map[Natural]) . (EX.sb) . (map[Natural])
  
  // the mapping preserves threads
  (EX_s.sthd) = ~(map[Natural]) . (EX.sthd) . (map[Natural])

  // the mapping preserves rfb
  all loc:Natural | EX.rfb[loc] = map[loc] . (EX_s.rfb[loc]) . ~(map[loc])

  // the mapping preserves tot, although more edges may be added
  // TODO: this is wrong
  EX.tot in (map[Natural]) . (EX_s.tot) . ~(map[Natural])
}

pred gp [EX:ExecJS, EX_s:ExecJS, map:Natural->EX.EV->EX_s.EV] {

  EX.sthd in *(EX.sb) + ~*(EX.sb)

  // some (EX.EV - EX.Tearfree)

  (consistent[EX])
  
  (consistent[EX_s])

  // We have a valid application of the mapping
  split_tearfree_execs[EX, EX_s, map]

}

// run gp for exactly 2 Exec, 2 ExecJS, 6 E, 6 Natural
