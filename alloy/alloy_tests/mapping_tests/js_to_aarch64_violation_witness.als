open memory_model_compare_js_aarch64 as compare

module alloy_tests/mapping_tests/js_to_aarch64_violation_witness

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

one sig ExecAArch64_Test_Stephen extends ExecAArch64 {} {

  ev_c in (W - L)

  (ev_a + ev_b + ev_d + ev_e) in L

  (ev_f + ev_g + ev_h) in A

  EV = ev_a + ev_b + ev_c + ev_d + ev_e + ev_f + ev_g + ev_h

  IW = none

  sb = ^((ev_a -> ev_b) + (ev_b -> ev_c)  + (ev_c -> ev_d) +
          (ev_e -> ev_f) + (ev_f -> ev_g)  + (ev_g -> ev_h))

  sthd = ((ev_a + ev_b + ev_c + ev_d) -> (ev_a + ev_b + ev_c + ev_d)) +
         ((ev_e + ev_f + ev_g + ev_h) -> (ev_e + ev_f + ev_g + ev_h))

  rfb = (loc_x -> ev_f -> ev_a) + (loc_z -> ev_g -> ev_d) + (loc_y -> ev_h -> ev_e)
}

pred gp[] {
  consistent[ExecAArch64_Test_Stephen]
  not consistent_stephen_unfixed[ExecJS_Test_Stephen]

  dead[ExecJS_Test_Stephen]
  not hard_dead[ExecJS_Test_Stephen]

  let map = (loc_x -> ev_a -> ev_a) +
         (loc_x -> ev_b -> ev_b) +
         (loc_y -> ev_c -> ev_c) +
         (loc_z -> ev_d -> ev_d) +
         (loc_y -> ev_e -> ev_e) +
         (loc_x -> ev_f -> ev_f) +
         (loc_z -> ev_g -> ev_g) +
         (loc_y -> ev_h -> ev_h) |

  compilation_mapping[ExecJS_Test_Stephen, ExecAArch64_Test_Stephen, map]
}

run gp for exactly 2 Exec, 8 E, 3 Natural
