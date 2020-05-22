open memory_model_js as js

module alloy_tests/js_tests/mixed/memory_module_js_test_Stephen_mixed

/*

Stephen_mixed:

ALLOWED/ALLOWED
(fixed/unfixed)

8 events, 4 locations

thread 1 {
a: write_sc [x]
b: write_sc [x]
c: write_sc [y1,y2]
d: write_sc [z]
}

thread 2 {
e: write_sc [y1]
f: read_sc [x] [a]
g: read_sc [z] [d]
h: read_sc [y1] [e]
}

f <_tot b 

*/

// disjoint locations x, y1, y2, and z
one sig loc_x extends Natural {}
one sig loc_y1 extends Natural {}
one sig loc_y2 extends Natural {}
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
  writes = loc_y1 + loc_y2
}

one sig ev_d extends E {} {
  no reads
  writes = loc_z
}

one sig ev_e extends E {} {
  no reads
  writes = loc_y1
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
  reads = loc_y1
  no writes
}

one sig ExecJS_Test_Stephen_mixed extends ExecJS {} {

  (ev_a + ev_b + ev_c + ev_d + ev_e + ev_f + ev_g + ev_h) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f + ev_g + ev_h

  IW = none

  sb = ^((ev_a -> ev_b) + (ev_b -> ev_c)  + (ev_c -> ev_d) +
          (ev_e -> ev_f) + (ev_f -> ev_g)  + (ev_g -> ev_h))

  sthd = ((ev_a + ev_b + ev_c + ev_d) -> (ev_a + ev_b + ev_c + ev_d)) +
         ((ev_e + ev_f + ev_g + ev_h) -> (ev_e + ev_f + ev_g + ev_h))

  rfb = (loc_x -> ev_f -> ev_a) + (loc_z -> ev_g -> ev_d) + (loc_y1 -> ev_h -> ev_e)

  (ev_f -> ev_b) in tot
}

pred test[] {
  some ExecJS_Test_Stephen_mixed

  consistent[ExecJS_Test_Stephen_mixed]

  consistent_stephen_unfixed[ExecJS_Test_Stephen_mixed]
}

run test for exactly 1 Exec, exactly 8 E, exactly 4 Natural

check { test[] } for exactly 1 Exec, exactly 8 E, exactly 4 Natural
