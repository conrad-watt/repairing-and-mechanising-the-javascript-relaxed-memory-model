open memory_model_js as js

module alloy_tests/js_tests/memory_module_js_test_ddagger

/*

ddagger:

NOT ALLOWED/ALLOWED
(fixed/unfixed)

6 events, 2 locations

thread 1 {
a: write_sc [x]
b: write_sc [y]
}

thread 2 {
c: write_sc [x]
d: read_sc [y] [b]
e: read [x] [d]
f: read [x] [a]
}

*/

// disjoint locations x and y
one sig loc_x extends Natural {}
one sig loc_y extends Natural {}

// disjoint events a,b,c,d,e,f
one sig ev_a extends E {} {
  no reads
  writes = loc_x
}

one sig ev_b extends E {} {
  no reads
  writes = loc_y
}

one sig ev_c extends E {} {
  no reads
  writes = loc_x
}

one sig ev_d extends E {} {
  reads = loc_y
  no writes
}

one sig ev_e extends E {} {
  reads = loc_x
  no writes
}

one sig ev_f extends E {} {
  reads = loc_x
  no writes
}

one sig ExecJS_Test_Ddagger extends ExecJS {} {

  ev_e + ev_f in Unord

  (ev_a + ev_b + ev_c + ev_d) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f

  IW = none

  sb = ^((ev_a -> ev_b) +
          (ev_c -> ev_d) + (ev_d -> ev_e) + (ev_e -> ev_f))

  sthd = ((ev_a + ev_b) -> (ev_a + ev_b)) +
         ((ev_c + ev_d + ev_e + ev_f) -> (ev_c + ev_d + ev_e + ev_f))

  rfb = (loc_y -> ev_d -> ev_b) + (loc_x -> ev_e -> ev_c) + (loc_x -> ev_f -> ev_a)
}

pred test[] {
  some ExecJS_Test_Ddagger

  not consistent[ExecJS_Test_Ddagger]

  consistent_sc_unfixed[ExecJS_Test_Ddagger]
}

run test for exactly 1 Exec, exactly 6 E, exactly 2 Natural

check { test[] } for exactly 1 Exec, exactly 6 E, exactly 2 Natural
