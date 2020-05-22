open memory_model_js as js

module alloy_tests/js_tests/memory_module_js_test_dagger

/*

dagger:

NOT ALLOWED/ALLOWED
(fixed/unfixed)

6 events, 2 locations

thread 1 {
a: write [x]
b: write_sc [y]
c: rmw [x] [a]
}

thread 2 {
d: read_sc [y] [b]
e: write_sc [x]
f: read_sc [x] [c]
}

e <_tot c 

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
  reads = loc_x
  writes = loc_x
}

one sig ev_d extends E {} {
  reads = loc_y
  no writes
}

one sig ev_e extends E {} {
  no reads
  writes = loc_x
}

one sig ev_f extends E {} {
  reads = loc_x
  no writes
}

one sig ExecJS_Test_Dagger extends ExecJS {} {

  ev_a in Unord

  (ev_b + ev_c + ev_d + ev_e + ev_f) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f

  IW = none

  sb = ^((ev_a -> ev_b) + (ev_b -> ev_c) +
          (ev_d -> ev_e) + (ev_e -> ev_f))

  sthd = ((ev_a + ev_b + ev_c) -> (ev_a + ev_b + ev_c)) +
         ((ev_d + ev_e + ev_f) -> (ev_d + ev_e + ev_f))

  rfb = (loc_x -> ev_c -> ev_a) + (loc_y -> ev_d -> ev_b) + (loc_x -> ev_f -> ev_c)

  (ev_e -> ev_c) in tot
}

pred test[] {
  some ExecJS_Test_Dagger

  not consistent[ExecJS_Test_Dagger]

  consistent_sc_unfixed[ExecJS_Test_Dagger]
}

run test for exactly 1 Exec, exactly 6 E, exactly 2 Natural

check { test[] } for exactly 1 Exec, exactly 6 E, exactly 2 Natural
