(* #!/usr/bin/env ocaml
 * #load "str.cma";;
 * #load "unix.cma";;
 * #load "yojson.cma";; *)

open Printf
open Unix
open Filename
open Yojson.Basic
open Yojson.Basic.Util



let spaces (n : int) : string = String.make n ' '

(* List utils *)


let concatMap (f : 'x -> 'y list) (l : 'x list) : 'y list =
  List.concat (List.map f l)

let rec optionMap (f : 'x -> 'y option) (l : 'x list) : 'y list =
  match l with
  | [] -> []
  | x :: xs ->
     match f x with
     | Some y -> y :: optionMap f xs
     | None -> optionMap f xs

(* https://ocaml.org/learn/tutorials/99problems.html *)
let rec range (a,b) =
  if a >= b then []
  else a :: range (a+1, b)

let range_fp (addr,size) = range (addr, addr+size)


(* Event kinds *)

type read_kind =
  | Read_plain
  | Read_acquire 
  | Read_exclusive 
  | Read_exclusive_acquire 
  | Read_stream
  | Read_weak_acquire

type write_kind =
  | Write_plain
  | Write_release 
  | Write_exclusive 
  | Write_exclusive_release

type barrier_kind =
  | Barrier_DMB
  | Barrier_DMB_ST
  | Barrier_DMB_LD
  | Barrier_ISB
  (* | Barrier_DSB
   * | Barrier_DSB_ST
   * | Barrier_DSB_LD *)

type kind =
  | Read of read_kind
  | Write of write_kind
  | Barrier of barrier_kind


let kind_of_string = function
  | "Read_plain" -> Read Read_plain
  | "Read_acquire" -> Read Read_acquire
  | "Read_exclusive" -> Read Read_exclusive
  | "Read_exclusive_acquire" -> Read Read_exclusive_acquire
  | "Read_stream" -> failwith "Read_stream"
  | "Read_weak_acquire" -> Read Read_weak_acquire

  | "Write_plain" -> Write Write_plain
  | "Write_release" -> Write Write_release
  | "Write_exclusive" -> Write Write_exclusive
  | "Write_exclusive_release" -> Write Write_exclusive_release

  | "Barrier_DMB" -> Barrier Barrier_DMB
  | "Barrier_DMB_ST" -> Barrier Barrier_DMB_ST
  | "Barrier_DMB_LD" -> Barrier Barrier_DMB_LD
  | "Barrier_DSB" -> failwith "Barrier_DSB"
  | "Barrier_DSB_ST" -> failwith "Barrier_DSB_ST"
  | "Barrier_DSB_LD" -> failwith "Barrier_DSB_LD"
  | "Barrier_ISB" -> Barrier Barrier_ISB

  | _ -> failwith "fail"


let is_read = function
  | Read _ -> true
  | _ -> false

let is_write = function
  | Write _ -> true
  | _ -> false

let is_barrier = function
  | Barrier _ -> true
  | _ -> false

let is_release_write = function
  | Write Write_release
  | Write Write_exclusive_release -> true
  | _ -> false

let is_weak_acquire = function
  | Read Read_acquire
  | Read Read_weak_acquire -> true
  | _ -> false

let is_strong_acquire = function
  | Read Read_acquire -> true
  | _ -> false

let is_dmb_full = function
  | Barrier Barrier_DMB -> true
  | _ -> false

let is_dmb_st = function
  | Barrier Barrier_DMB_ST -> true
  | _ -> false

let is_dmb_ld = function
  | Barrier Barrier_DMB_LD -> true
  | _ -> false

let is_isb = function
  | Barrier Barrier_ISB -> true
  | _ -> false


(* Events *)

type id =
  | Init
  | Id of (int * int * int)

type loc = int
type size = int
type fp  = loc * size

type event = id * fp option * kind

let is_event (p : kind -> bool) (e : event) : bool = 
  let (_,_,kind) = e in
  p kind


let make_id (a,b,c) = 
  if a = 1000 then Init else Id (a,b,c)

let name = function
  | Id (a,b,c) -> sprintf "ev_%d_%d_%d" a b c
  | Init -> "ev_I"


(* Executions *)

type execution = {
    events : event list;
    locations : loc list;
    w : id list;
    r : id list;
    l : id list;
    a : id list;
    q : id list;
    dmb_full : id list;
    dmb_st : id list;
    dmb_ld : id list;
    isb : id list;
    ev : id list;
    iw : id list;
    po : (id * id) list;
    same_thread : (id * id) list;
    same_instr : (id * id) list;
    addr : (id * id) list;
    data : (id * id) list;
    ctrl : (id * id) list;
    rf : (loc * id * id) list;
    co : (id * id) list;
    rmw : (id * id) list;
  }


(* Extract from json *)

let json_fp_to_fp (fp : json) : fp = 
  let addr = fp |> member "addr" |> to_int in
  let size = fp |> member "size" |> to_int in
  (addr,size)

let fp_of_json_event (json : json) : fp option =
  try 
    let fp = json |> member "fp" in
    Some (json_fp_to_fp fp)
  with
  | _ -> None


let json_id_to_id id = 
  match id |> to_list |> filter_int with
  | [a;b;c] -> make_id (a,b,c)
  | _ -> failwith "not an ID"

let id_of_json_event (json : json) : id =
  json |> member "id" |> json_id_to_id


let kind_of_json_event e = 
  let typ = e |> member "type" |> to_string in
  kind_of_string typ
  

let json_event_to_event (e : json) = 
  let kind = kind_of_json_event e in
  let fp = fp_of_json_event e in
  let id = id_of_json_event e in
  match id with
  | Init -> None
  | _ -> Some (id, fp, kind)


let json_id_tuple_to_id_tuple (tuple : json) : (id * id) =
  match to_list tuple with
  | [a;b] -> (json_id_to_id a, json_id_to_id b)
  | _ -> failwith "not a binary relation"


let json_rf_item_to_rf_item (rf_item : json) : (loc * id * id) list  = 
  let fp = rf_item |> member "fp" |> json_fp_to_fp in
  let write = rf_item |> member "write" |> json_id_to_id in
  let read = rf_item |> member "read" |> json_id_to_id in
  List.map (fun l -> (l,read,write)) (range_fp fp)


let events_of_execution (json : json) : event list =
  (json |> member "events" |> to_list |> optionMap json_event_to_event)

let binrel_of_execution name (json : json) : (id * id) list =
  json |> member name |> to_list |> (List.map json_id_tuple_to_id_tuple)

let rf_of_execution (json : json) : (loc * id * id) list =
  json |> member "rf" |> to_list |> (concatMap json_rf_item_to_rf_item)


let location_of_event event : int list = 
  match event with
  | (_, Some fp, _) -> range_fp fp
  | (_, None, _) -> []

let locations_of_events events : int list =
  let locations = concatMap location_of_event events in
  List.sort_uniq compare locations


let matching_ids (p : kind -> bool) (es : event list) : id list =
  let filtered = List.filter (is_event p) es in
  List.map (fun (id,_,_) -> id) filtered

let execution_of_json_execution (json : json) : execution =
  let events : event list = events_of_execution json in
  { events = events
  ; w = Init :: matching_ids is_write events
  ; r = matching_ids is_read events
  ; l = matching_ids is_release_write events
  ; a = matching_ids is_strong_acquire events 
  ; q = matching_ids is_weak_acquire events
  ; dmb_full = matching_ids is_dmb_full events
  ; dmb_st = matching_ids is_dmb_st events
  ; dmb_ld = matching_ids is_dmb_ld events
  ; isb = matching_ids is_isb events
  ; ev = Init :: matching_ids (fun _ -> true) events
  ; iw = [Init]
  ; locations = locations_of_events events
  ; po = binrel_of_execution "po" json
  ; same_thread =
      List.filter (fun (id,id') -> id <> Init && id' <> Init)
        (binrel_of_execution "same_thread" json)
  ; same_instr = binrel_of_execution "same_instr" json
  ; addr = binrel_of_execution "addr" json
  ; data = binrel_of_execution "data" json
  ; ctrl = binrel_of_execution "ctrl" json
  ; rf = rf_of_execution json
  ; co = binrel_of_execution "co" json
  ; rmw = binrel_of_execution "rmw" json
  }


let executions_of_json (json : json) : execution list =
  json |> member "executions" |> to_list
       |> List.map execution_of_json_execution



(* from http://www.codecodex.com/wiki/Replace_or_remove_all_occurrences_of_a_string#OCaml *)
let replace (to_replace : string) (withS : string) : string -> string =
  Str.global_replace (Str.regexp_string to_replace) withS

(* Print things *)

let header original_testname testname = 
  "open memory_model_aarch64 as aarch64\n\n" ^
  "module json_tests/" ^ 
  testname ^ "\n\n"

let loc i = sprintf "loc_%d" i

let op_list 
      (op : string)
      ?(multiline_indent : int option = None) 
      (f : 'x -> string)
      (xs : 'x list) 
    : string =
  match xs, multiline_indent with
  | [],_ -> "none"
  | _, None -> String.concat op (List.map f xs)
  | _, Some n -> 
     let spc = spaces n in
     "\n" ^ spc ^ String.concat (op ^ " \n" ^ spc) (List.map f xs)


let declare_location l = 
  sprintf "one sig %s in Natural {}\n" (loc l)

let declare_locations_disjoint ls = 
  "fact {\n" ^
  "  disj[" ^
    (op_list ", " ~multiline_indent:(Some 4) loc ls) ^ "\n" ^
  "  ]\n" ^
  "}\n"

let declare_locations locations =
  String.concat "\n" (List.map declare_location locations) ^ "\n" ^
  declare_locations_disjoint locations


let declare_event ((id, _, kind) as event) = 
  let (reads, writes) = match kind with
    | Read _ ->
       ("reads = " ^ op_list " + " loc (location_of_event event), "no writes")
    | Write _ ->
       ("no reads", "writes = " ^ op_list " + " loc (location_of_event event))
    | Barrier _ ->
       ("no reads", "no writes")
  in
  "one sig " ^ name id ^ " extends E {} {\n" ^
  "  " ^ reads ^ "\n" ^
  "  " ^ writes ^ "\n" ^
  "}\n"


let declare_events events =
  String.concat "\n" (List.map declare_event events) ^ "\n\n" ^
  "one sig " ^ name Init ^ " extends E {}\n"

let declare_unirel (relname : string) (rel : id list) : string = 
  "  " ^ relname ^ " = " ^
    op_list " + " ~multiline_indent:(Some 4) name rel ^ "\n"

let declare_binrel_item (id1,id2) : string =
  "(" ^ name id1 ^ " -> " ^ name id2 ^ ")" 

let declare_binrel (relname : string) (rel : (id * id) list) : string =
  match rel with
  | [] -> "  no " ^ relname ^ "\n"
  | _ -> 
    "  " ^ relname ^ " = " ^ 
      op_list " + " ~multiline_indent:(Some 4) declare_binrel_item rel ^ "\n"

let declare_rf_item (l,read,write) : string =
  "(" ^ loc l ^ " -> " ^ name read ^ " -> " ^ name write ^ ")"   

let declare_rf (rel : (loc * id * id) list) : string =
  match rel with
  | [] -> "  no rf\n"
  | _ ->
    "  rfb = " ^ op_list " + " ~multiline_indent:(Some 4) declare_rf_item rel ^ "\n"


let declare_execution_object execution_name execution =
  "one sig " ^ execution_name ^ " extends ExecAArch64 {} {\n\n" 
  ^
  String.concat "\n"
    [declare_unirel "R" execution.r
    ; declare_unirel "W" execution.w
    ; declare_unirel "L" execution.l
    ; declare_unirel "A" execution.a
    ; declare_unirel "Q" execution.q
    ; declare_unirel "B_dmb_full" execution.dmb_full
    ; declare_unirel "B_dmb_st" execution.dmb_st
    ; declare_unirel "B_dmb_ld" execution.dmb_ld
    ; declare_unirel "B_isb" execution.isb
    ; declare_unirel "EV" execution.ev
    ; declare_unirel "IW" execution.iw
    ; declare_binrel "sb" execution.po (* named sb in model *)
    ; declare_binrel "sthd" execution.same_thread (* named sthd in model *)
    ; declare_binrel "si" execution.same_instr (* named si in model *)
    ; declare_binrel "addr'" execution.addr
    ; declare_binrel "data'" execution.data
    ; declare_binrel "ctrl'" execution.ctrl
    ; declare_rf execution.rf (* named rfb in model *)
    ; declare_binrel "co" execution.co
    ; declare_binrel "rmw" execution.rmw
    ]
  ^
  "}\n\n"

let declare_execution execution_name execution = 
  String.concat "\n"
    [ declare_locations execution.locations
    ; declare_events execution.events
    ; declare_execution_object execution_name execution
    ]

let declare_pred execution_name = 
  "pred test[] {\n" ^
  "  some " ^ execution_name ^ "\n" ^ 
  "  consistent[" ^ execution_name ^ "]\n" ^ 
  "}\n"

let stupid_smallest_vector_width_to_distinct n = 
  assert (n >= 0);
  match n with
  | 0  -> 1

  | 1  -> 2

  | 2  -> 3
  | 3  -> 3

  | 4  -> 4
  | 5  -> 4
  | 6  -> 4
  | 7  -> 4

  | 8  -> 5
  | 9  -> 5
  | 10 -> 5
  | 11 -> 5
  | 12 -> 5
  | 13 -> 5
  | 14 -> 5
  | 15 -> 5

  | 16 -> 6
  | 17 -> 6
  | 18 -> 6
  | 19 -> 6
  | 20 -> 6
  | 21 -> 6
  | 22 -> 6
  | 23 -> 6
  | 24 -> 6
  | 25 -> 6
  | 26 -> 6
  | 27 -> 6
  | 28 -> 6
  | 29 -> 6
  | 30 -> 6
  | 31 -> 6

  | 32 -> 7
  | 33 -> 7
  | 34 -> 7
  | 35 -> 7
  | 36 -> 7
  | 37 -> 7
  | 38 -> 7
  | 39 -> 7
  | 40 -> 7
  | 41 -> 7
  | 42 -> 7
  | 43 -> 7
  | 44 -> 7
  | 45 -> 7
  | 46 -> 7
  | 47 -> 7
  | 48 -> 7
  | 49 -> 7
  | 50 -> 7
  | 51 -> 7
  | 52 -> 7
  | 53 -> 7
  | 54 -> 7
  | 55 -> 7
  | 56 -> 7
  | 57 -> 7
  | 58 -> 7
  | 59 -> 7
  | 60 -> 7
  | 61 -> 7
  | 62 -> 7
  | 63 -> 7
  | n  -> failwith "too complicated"




let declare_run (execution_name : string) (execution : execution) = 
  let number_locations = List.length execution.locations in
  let number_events = List.length execution.ev in
  let vector_width = stupid_smallest_vector_width_to_distinct number_locations in
  (sprintf "run test for exactly 1 Exec, exactly %d E, exactly %d Natural, %d Int\n"
     number_events number_locations vector_width)
(*^
  (sprintf "check { test[] } for exactly 1 Exec, exactly %d E, exactly %d Natural\n"
     number_events number_locations) *)

let normalise_name name =
  name |>
    replace "+" "_Plus_" |>
    replace "." "_Dot_" |>
    replace "-" "_Minus_" |>
    replace "[" "_Lbrack_" |>
    replace "]" "_Rbrack_" |>
    (^) "Test_"

(* from https://ocaml.org/learn/tutorials/file_manipulation.html *)
 let write_file file string =
   let oc = open_out file in
   fprintf oc "%s\n" string;
   close_out oc

let print_execution (dir_name : string) (execution_name : string) (execution : execution) =
  let fixed_execution_name = normalise_name execution_name
  in
  let s = 
    header execution_name fixed_execution_name ^ "\n\n" ^ 
    declare_execution fixed_execution_name execution ^ "\n\n" ^ 
    declare_pred fixed_execution_name ^ "\n\n" ^
    declare_run fixed_execution_name execution
  in
  write_file ((Filename.concat dir_name execution_name) ^ ".als") s

let print_executions dirname basename executions =
  print_endline ("processing test \"" ^ basename ^ "\"");
  List.iteri
    (fun n e -> print_execution dirname (basename^string_of_int n) e)
    executions


let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)


let parse_file : string -> json = from_file

let process_file dirname filename = 
  let _ = syscall ("mkdir -p " ^ dirname) in
  let json = parse_file filename in
  let name = Filename.remove_extension filename in
  print_executions dirname (Filename.basename name) (executions_of_json json)

let main = 
  if (Array.length Sys.argv < 3)
  then failwith "usage <outdir> <file argument>"
  else 
    let outdir = Sys.argv.(1) in
    Array.iteri (fun i f -> if i > 1 then process_file outdir f else ()) Sys.argv
