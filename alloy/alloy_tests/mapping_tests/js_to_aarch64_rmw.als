open memory_model_compare_js_aarch64 as compare

module alloy_tests/mapping_tests/js_to_aarch64_rmw

// one location, x
one sig loc_x extends Natural {}

// disjoint events a,b,b_r,b_w,c,d,e
one sig ev_a extends E {} {
  no reads
  writes = loc_x
}
one sig ev_b extends E {} {
  reads = loc_x
  writes = loc_x
}

one sig ev_b_r extends E {} {
  reads = loc_x
  no writes
}

one sig ev_b_w extends E {} {
  no reads
  writes = loc_x
}

one sig ev_c extends E {} {
  reads = loc_x
  no writes
}

one sig ev_d extends E {} {
  no reads
  writes = loc_x
}

one sig ev_e extends E {} {
  reads = loc_x
  no writes
}

one sig ExecJS_Test_RMW extends ExecJS {} {

  (ev_a + ev_b + ev_c + ev_d + ev_e) in SC

  EV = ev_a + ev_b + ev_c + ev_d + ev_e

  IW = none

  sb = ^((ev_a -> ev_b) + (ev_c -> ev_d)  + (ev_d -> ev_e))

  sthd = ((ev_a + ev_b) -> (ev_a + ev_b)) +
         ((ev_c + ev_d + ev_e) -> (ev_c + ev_d + ev_e))

  rfb = (loc_x -> ev_c -> ev_a) + (loc_x -> ev_b -> ev_a) + (loc_x -> ev_e -> ev_b)

  // (ev_f -> ev_b) in tot
}

one sig ExecAArch64_Test_RMW extends ExecAArch64 {} {

  (ev_a + ev_b_w + ev_d) in L

  (ev_b_r + ev_c + ev_e) in A

  EV = ev_a + ev_b_r + ev_b_w + ev_c + ev_d + ev_e

  IW = none

  sb = ^((ev_a -> ev_b_r) + (ev_b_r -> ev_b_w)  + (ev_c -> ev_d) + (ev_d -> ev_e))

  sthd = ((ev_a + ev_b_r + ev_b_w) -> (ev_a + ev_b_r + ev_b_w)) +
         ((ev_c + ev_d + ev_e) -> (ev_c + ev_d + ev_e))

  rfb = (loc_x -> ev_c -> ev_a) + (loc_x -> ev_b_r -> ev_a) + (loc_x -> ev_e -> ev_b_w)

  rmw = (ev_b_r -> ev_b_w)
}

pred gp[] {
  consistent[ExecAArch64_Test_RMW]

  not consistent[ExecJS_Test_RMW]

  // dead[ExecJS_Test_Stephen]
  // not hard_dead[ExecJS_Test_Stephen]

  let map = (loc_x -> ev_a -> ev_a) +
         (loc_x -> ev_b -> ev_b_r) +
         (loc_x -> ev_b -> ev_b_w) +
         (loc_x -> ev_c -> ev_c) +
         (loc_x -> ev_d -> ev_d) +
         (loc_x -> ev_e -> ev_e) |

  compilation_mapping_tot[ExecJS_Test_RMW, ExecAArch64_Test_RMW, map]
}

run gp for exactly 2 Exec, 7 E, 1 Natural
