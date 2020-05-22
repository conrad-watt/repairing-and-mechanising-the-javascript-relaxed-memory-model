open memory_model_js as js

module alloy_tests/js_tests/mixed/memory_module_js_test_ddagger_mixed

/*

ddagger_mixed:

ALLOWED/ALLOWED
(fixed/unfixed)

6 events, 3 locations

thread 1 {
a: write_sc [x1]
b: write_sc [y]
}

thread 2 {
c: write_sc [x1,x2]
d: read_sc [y] [b]
e: read [x1] [d]
f: read [x1] [a]
}

*/

// disjoint locations x1, x2, and y
one sig loc_x1 extends Natural {}
one sig loc_x2 extends Natural {}
one sig loc_y extends Natural {}

// disjoint events a,b,c,d,e,f
one sig ev_a extends E {} {
  no reads
  writes = loc_x1
}

one sig ev_b extends E {} {
  no reads
  writes = loc_y
}

one sig ev_c extends E {} {
  no reads
  writes = loc_x1 + loc_x2
}

one sig ev_d extends E {} {
  reads = loc_y
  no writes
}

one sig ev_e extends E {} {
  reads = loc_x1
  no writes
}

one sig ev_f extends E {} {
  reads = loc_x1
  no writes
}

one sig ExecJS_Test_Ddagger_mixed extends ExecJS {} {

  ev_e + ev_f in Unord

  (ev_a + ev_b + ev_c + ev_d) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f

  IW = none

  sb = ^((ev_a -> ev_b) +
          (ev_c -> ev_d) + (ev_d -> ev_e) + (ev_e -> ev_f))

  sthd = ((ev_a + ev_b) -> (ev_a + ev_b)) +
         ((ev_c + ev_d + ev_e + ev_f) -> (ev_c + ev_d + ev_e + ev_f))

  rfb = (loc_y -> ev_d -> ev_b) + (loc_x1 -> ev_e -> ev_c) + (loc_x1 -> ev_f -> ev_a)
}

pred test[] {
  some ExecJS_Test_Ddagger_mixed

  consistent[ExecJS_Test_Ddagger_mixed]

  consistent_sc_unfixed[ExecJS_Test_Ddagger_mixed]
}

run test for exactly 1 Exec, exactly 6 E, exactly 3 Natural

check { test[] } for exactly 1 Exec, exactly 6 E, exactly 3 Natural
