open memory_model_js as js

module alloy_tests/js_tests/memory_module_js_test_Stephen

/*

Stephen:

ALLOWED/NOT ALLOWED
(fixed/unfixed)

8 events, 3 locations

thread 1 {
a: write_sc [x]
b: write_sc [x]
c: write [y]
d: write_sc [z]
}

thread 2 {
e: write_sc [y]
f: read_sc [x] [a]
g: read_sc [z] [d]
h: read_sc [y] [e]
}

f <_tot b 

*/

// disjoint locations x, y, and z
one sig loc_x extends Natural {}
one sig loc_y extends Natural {}
one sig loc_z extends Natural {}

// disjoint events a,b,c,d,e,f,g,h
one sig ev_a extends E {} {
  no reads
  writes = loc_x
}

one sig ev_b extends E {} {
  no reads
  writes = loc_x
}

one sig ev_c extends E {} {
  no reads
  writes = loc_y
}

one sig ev_d extends E {} {
  no reads
  writes = loc_z
}

one sig ev_e extends E {} {
  no reads
  writes = loc_y
}

one sig ev_f extends E {} {
  reads = loc_x
  no writes
}

one sig ev_g extends E {} {
  reads = loc_z
  no writes
}

one sig ev_h extends E {} {
  reads = loc_y
  no writes
}

one sig ExecJS_Test_Stephen extends ExecJS {} {

  ev_c in Unord

  (ev_a + ev_b + ev_d + ev_e + ev_f + ev_g + ev_h) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f + ev_g + ev_h

  IW = none

  sb = ^((ev_a -> ev_b) + (ev_b -> ev_c)  + (ev_c -> ev_d) +
          (ev_e -> ev_f) + (ev_f -> ev_g)  + (ev_g -> ev_h))

  sthd = ((ev_a + ev_b + ev_c + ev_d) -> (ev_a + ev_b + ev_c + ev_d)) +
         ((ev_e + ev_f + ev_g + ev_h) -> (ev_e + ev_f + ev_g + ev_h))

  rfb = (loc_x -> ev_f -> ev_a) + (loc_z -> ev_g -> ev_d) + (loc_y -> ev_h -> ev_e)

  (ev_f -> ev_b) in tot
}

pred test[] {
  some ExecJS_Test_Stephen

  consistent[ExecJS_Test_Stephen]

  not consistent_stephen_unfixed[ExecJS_Test_Stephen]
}

run test for exactly 1 Exec, exactly 8 E, exactly 3 Natural

check { test[] } for exactly 1 Exec, exactly 8 E, exactly 3 Natural
