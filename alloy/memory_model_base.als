open util/natural as natural
open relations[E] as relations

// locations are just naturals

// note: this doesn't fix the number of locations
lone sig Two in Natural {}
lone sig Three in Natural {}
lone sig Four in Natural {}
lone sig Five in Natural {}
lone sig Six in Natural {}
lone sig Seven in Natural {}
lone sig Eight in Natural {}

fact {
  natural/next[One] in Two
  add[Two,One] in Three
  add[Two,Two] in Four
  add[Three,Two] in Five
  add[Three,Three] in Six
  add[Four,Three] in Seven
  add[Four,Four] in Eight
}

let range[start,end] = {  i : Natural | gte[i,start] and lte[i,end] }

sig E {
  reads : set Natural,
  writes : set Natural,
  
}{
  // an event at least reads or writes
  // some reads || some writes

  // RMW events are to one range
  (some reads && some writes) => (reads = writes)

  // reads are to contiguous locations
  some reads => (some start,end : Natural | reads = range[start,end])

  // writes are to contiguous locations
  some writes => (some start,end : Natural | writes = range[start,end])

}

pred reading[X : E] { some (X.reads) }
pred writing[X : E] { some (X.writes) }
pred rmw[X : E] { reading[X] && writing[X] }

fun e_range[X : E] : set Natural { X.reads + X .writes }

pred no_rem[X,Y:Natural] {
  mul[div[X,Y],Y] = X
}

fun e_range_diff[X : E] : Natural { sub[ max[e_range[X]], min[e_range[X]] ] }

pred size_one[X : E] {
  e_range_diff[X] = Zero
}

pred size_two[X : E] {
  e_range_diff[X] = One
}

pred size_four[X : E] {
  e_range_diff[X] = Three
}

pred size_eight[X : E] {
  e_range_diff[X] = Seven
}

pred aligned_one[X : E] {
  size_one[X]
}

pred aligned_two[X : E] {
  no_rem[ min[e_range[X]], Two ] && size_two[X]
}

pred aligned_four[X : E] {
  no_rem[ min[e_range[X]], Four ] && size_four[X]
}

pred aligned_eight[X : E] {
  no_rem[ min[e_range[X]], Eight ] && size_eight[X]
}


sig Exec {
  EV : set E,    // domain of all events
  W, R : set EV, // writes, reads
  IW : lone W,   // optional initial write
  sb : EV -> EV,  // sequenced before
  sthd : EV -> EV,  // same thread (partial E.R)
  // si : EV -> EV, // same instruction
  rfb : Natural -> R -> lone W, // reads at location
  rf : R -> W // reads-from, derived from rfb
} {

  // every event reads or writes
  // EV = W + R

  // every non-initializing event is 1/2/4/8* bytes
  all X:((R+W)-IW) | (size_one[X] || size_two[X] || size_four[X] || size_eight[X])

  // W and R are well-formed
  R = { X:EV | reading[X] }
  W = { X:EV | writing[X] }

  one IW => {
  // the initial write is to all locations
  IW.reads = none
  IW.writes = Natural
  }

  // the initial event is an ordinary write
  IW in W - R

  // sthd is an equivalence relation among non-initial events
  is_equivalence[sthd, EV - IW]

  // sequenced-before is intra-thread
  sb in sthd

  // sequenced-before is acyclic and transitive
  strict_partial_order[sb]

  /* TODO: re-evaluate same-instruction
  // same-instruction is intra-thread
  si in (sthd + (IW -> IW))

  // same-instruction is an equivalence relation on events
  is_equivalence[si, EV]

  // nothing is related by both sequenced-before and same-instruction
  no (si & sb)

  // intra-thread: everything is either related by sequenced-before, or same-instruction
  sthd in *(sb) + (~*(sb)) + si
  // Every event must be aligned
  all X:EV | (aligned_one[X] || aligned_two[X] || aligned_four[X]) // || aligned_eight[X]
  // intra-thread: everything is related by sequenced-before
  sthd in *(sb) + (~*(sb))
  */

  // rfb is well-formed
  all X:R, loc:Natural | loc in X.reads => ( some Y:rfb[loc,X] | (loc in X.reads && loc in Y.writes && !(X=Y) ) ) else no rfb[loc,X]

  //rf is derived from the projection of rfb
  rf = rfb[Natural]
}

fun evs_loc[es:set E, loc:Natural] : set es {
  {X:es | loc in X.e_range }
}

pred gp {
 some Exec
}

// run gp for 1 Exec, 6 E, 6 Natural
