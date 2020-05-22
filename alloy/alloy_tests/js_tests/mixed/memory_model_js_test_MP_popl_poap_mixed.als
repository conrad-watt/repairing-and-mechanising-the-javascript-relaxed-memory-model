open memory_model_js as js

module alloy_tests/js_tests/mixed/memory_module_js_test_MP_popl_poap

/*

MP+popl+poap_mixed:

ALLOWED

5 events, 3 locations

i: init 0

thread 1 {
a: write [x]
b: write_sc [y1]
}

thread 2 {
c: read_sc [y1,y2] [b,i]
d: read [x] [i]
}

*/

// disjoint locations x, y1, and y2
one sig loc_x extends Natural {}
one sig loc_y1 extends Natural {}
one sig loc_y2 extends Natural {}

// disjoint events a,b,c,d
one sig ev_a extends E {} {
  no reads
  writes = loc_x
}

one sig ev_b extends E {} {
  no reads
  writes = loc_y1
}

one sig ev_c extends E {} {
  reads = loc_y1 + loc_y2
  no writes
}

one sig ev_d extends E {} {
  reads = loc_x
  no writes
}

sig ev_i extends E {}

one sig ExecJS_Test_MP_popl_poap_mixed extends ExecJS {} {

  (ev_a + ev_d) in Unord
  (ev_b + ev_c) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_i

  IW = ev_i

  sb = (ev_a -> ev_b) + (ev_c -> ev_d)

  sthd = ((ev_a + ev_b) -> (ev_a + ev_b)) + ((ev_c + ev_d) -> (ev_c + ev_d))

  rfb = (loc_y1 -> ev_c -> ev_b) + (loc_y2 -> ev_c -> ev_i) + (loc_x -> ev_d -> ev_i)
}

pred test[] {
  some ExecJS_Test_MP_popl_poap_mixed

  consistent[ExecJS_Test_MP_popl_poap_mixed]
}

run test for exactly 1 Exec, exactly 5 E, exactly 3 Natural

check { test[] } for exactly 1 Exec, exactly 5 E, exactly 3 Natural
