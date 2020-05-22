open memory_model_base as memory

sig ExecAArch64 extends Exec {

  si : EV -> EV, // same-instruction (unused)

  rfi : W -> R,
  rfe: W -> R,

  frb : Natural -> R -> W,
  fr : R -> W, // from-reads
  fre : R -> W,

  cob : Natural -> W -> W,
  co : W -> W, // coherence
  coi : W -> W,
  coe : W -> W,

  addr' : (R+W) -> (R+W), // address dependency
  data' : (R+W) -> W, // data dependency
  ctrl' : (R+W) -> EV, // control dependency

  // versions restricted to reads on the left
  addr : R -> (R+W), // address dependency
  data : R -> W, // data dependency
  ctrl : R -> EV, // control dependency

  ca : (R+W) -> W, // coherence-after

  obs : (R+W) -> (R+W), // observed-by

  dob : R -> EV, // dependency-ordered-before
  
  aob : (R+W) -> (R+W), // atomic-ordered-before
  rmw : R -> W, // rmw

  bob : EV -> EV, // barrier-ordered-before

  iob : IW -> EV, // initial-write-ordered-before

  ob : EV -> EV, // ordered-before

  polocb : Natural -> (R+W) -> (R+W), // program-order-per-location

  // consistency modes
  A : set R, // strong acquire loads
  Q : set R, // weak acquire loads
  L : set W, // release stores

  // TODO: make these sets non-empty
  B_dmb_full : set (EV - (R + W)), // full barrier
  B_dmb_ld : set (EV - (R + W)), // load barrier
  B_dmb_st : set (EV - (R + W)), // store barrier
  B_isb : set (EV - (R + W)) // instruction sync barrier

}{
  let po = sb {

  // Every event must be aligned
  all X:(R+(W-IW)) | (aligned_one[X] || aligned_two[X] || aligned_four[X] || aligned_eight[X])

  // strong acquire loads are a subset of weak acquire loads
  A in Q

  // the initial write is an ordinary write
  IW in (W - L)

  addr = R <: addr'
  data = R <: data'
  ctrl = R <: ctrl'

  // there are no native rmw events in AArch64, and barrier types are exclusive
  disj[R, W, B_dmb_full, B_dmb_ld, B_dmb_st, B_isb]

  all X:(B_dmb_full + B_dmb_ld + B_dmb_st + B_isb) | no e_range[X]

  // beware!!! rf and rfb are the opposite way around from what is expected

  // byte-wise coherence is a per-location total order on writes
  all loc:Natural | strict_total_order[ cob[loc], { E:W | loc in E.writes } ]
  all loc:Natural, W1,W2:W | (W1 -> W2) in cob[loc] => (loc in W1.writes && loc in W2.writes)

  // coherence is the transitive closure of cob projected
  co = ^(cob[Natural])

  // coherence is a strict partial order (restricts cob)
  strict_partial_order[co]

  coi = (co & sthd)
  coe = co - coi

  // flipped rf used here
  rfi = ((~rf) & sthd)
  rfe = (~rf) - rfi

  // flipped rfb used here
  all loc:Natural | frb[loc] = ((rfb[loc]) . (cob[loc]))

  fr = frb[Natural]
  // fri = (fr & sthd)
  fre = fr - (fr & sthd)

  ca = (fr+co)

  obs = (rfe + fre + coe)

  dob = addr +
         data +
         (ctrl :> W) + ((((ctrl + (addr.po)) :> B_isb)).(po :> R)) +
         (addr.(po :> W)) + ((ctrl + data).coi) +
         ((addr + data).rfi)

  aob = rmw + (rmw[R] <: (rfi :> (A + Q)))

  bob = (po :> B_dmb_full).po +
         ((L <: po) :> A) +
         ((R <: po) :> B_dmb_ld).po +
         Q <: po +
         ((((W <: po) :> B_dmb_st).po) :> W) +
         (po :> L) +
         (po :> L).coi

  iob = (IW -> (EV - IW))

  ob = obs +
        dob +
        aob +
        bob +
        iob

  polocb = {loc:Natural, E1:EV, E2:EV | (E1->E2) in po && loc in E1.e_range && loc in E2.e_range }

  rmw in po
  addr in po
  data in po
  ctrl in po
}}

pred consistent[EX:ExecAArch64]{

  // single copy atomicity
  // don't check for cycles
  // flipped rf used here
  irreflexive[((~(EX.rf)).(EX.fr))]

  // internal visibility
  // flipped rfb used here
  all loc:Natural | is_acyclic[(EX.polocb[loc] + EX.frb[loc] + EX.cob[loc] + (~((EX.rfb)[loc])))]

  // external visibility
  is_acyclic[EX.ob]

  // no intervening writes for load/store exclusives
  no (EX.rmw & ((EX.fre).(EX.coe)))

}

// ----------------------------------------------------------------------

pred gp [EX:ExecAArch64] {

  EX.sthd in *(EX.sb) + ~*(EX.sb)

  // some (EX.EV - EX.Tearfree)

  (consistent[EX])

}

// run gp for exactly 1 Exec, exactly 6 E, 6 Natural
