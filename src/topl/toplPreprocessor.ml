(* modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

module A = Topl.PropAst

(* }}} *)
(* globals *) (* {{{ *)
let out_dir = ref "out"

(* }}} *)
(* used to communicate between conversion and instrumentation *) (* {{{ *)
type method_ =  (* TODO: Use [PropAst.event_tag] instead? *)
  { method_name : string
  ; method_arity : int }

(* }}} *)
(* representation of automata in Java *) (* {{{ *)

(*
  The instrumenter has three phases:
    - convert the automaton to an intermediate representation
    - instrument the bytecode
    - emit the Java representation of the automaton
  A pattern like "c.m()" in the property matches method m in all classes that
  extend c (including c itself). For efficiency, the Java automaton does not
  know anything about inheritance. While the bytecode is instrumented all the
  methods m in classes extending c get unique identifiers and the pattern
  "c.m()" is mapped to the set of those identifiers.

  The (first) conversion
    - goes from edge list to adjacency list
    - glues all input properties into one
    - changes the vertex representation from strings to integers
    - changes automaton variable representation from strings to integers
    - normalizes method patterns (by processing "using prefix", ... )
    - collects all patterns
  During printing a bit more processing is needed to go to the Java
  representation, but only very simple stuff.
 *)

(* shorthands for old types, those that come from prop.mly *)
type property = (string, string) A.t
type tag_guard = A.pattern A.tag_guard

(* shorthands for new types, those used in Java *)
type tag = int
type vertex = int
type variable = int
type value = string (* Java literal *)

type transition =
  { steps : (A.pattern, variable, value) A.label list
  ; target : vertex }

type vertex_data =
  { vertex_property : property
  ; vertex_name : A.vertex
  ; outgoing_transitions : transition list }

type automaton =
  { vertices : vertex_data array
  ; observables : (property, tag_guard) Hashtbl.t
  ; pattern_tags : (tag_guard, tag list) Hashtbl.t
  (* The keys of [pattern_tags] are filled in during the initial conversion,
    but the values (the tag list) is filled in while the code is being
    instrumented. *)
  ; event_names : (int, string) Hashtbl.t }

let check_automaton x =
  let rec is_decreasing x = function
    | [] -> true
    | y :: ys -> x >= y && is_decreasing y ys in
  let ok _ v = assert (is_decreasing max_int v) in
  Hashtbl.iter ok x.pattern_tags

(* }}} *)
(* small functions that help handling automata *) (* {{{ *)
let to_ints xs =
  let h = Hashtbl.create 101 in
  let c = ref (-1) in
  let f x = if not (Hashtbl.mem h x) then (incr c; Hashtbl.add h x !c) in
  List.iter f xs; h

let inverse_index f h =
  let r = Array.make (Hashtbl.length h) None in
  let one k v = assert (r.(v) = None); r.(v) <- Some (f k) in
  Hashtbl.iter one h;
  Array.map from_some r

let get_properties x =
  x.vertices |> Array.map (fun v -> v.vertex_property) |> Array.to_list

let get_vertices p =
  let f acc t = t.A.source :: t.A.target :: acc in
  "start" :: "error" :: List.fold_left f [] p.A.transitions

(* }}} *)
(* pretty printing to Java *) (* {{{ *)

let pp_option pp_e f = function
  | None -> fprintf f "None"
  | Some s -> fprintf f "Some(%a)" pp_e s

type 'a pp_index =
  { to_int : 'a -> int
  ; of_int : int -> 'a
  ; count : int }

type pp_full_index =
  { idx_constant : value pp_index
  ; idx_string : string pp_index }

let array_foldi f z xs =
  let r = ref z in
  for i = 0 to Array.length xs - 1 do r := f !r i xs.(i) done;
  !r

let starts x =
  let f ks k = function
    | {vertex_name="start";_} -> k :: ks
    | _ -> ks in
  array_foldi f [] x.vertices

let errors x =
  let f = function
    | {vertex_name="error"; vertex_property={A.message=e;_};_} -> Some e
    | _ -> None in
  x.vertices |> Array.map f |> Array.to_list

let rec pp_v_list pe ppf = function
  | [] -> ()
  | [x] -> fprintf ppf "@\n%a" pe x
  | x :: xs -> fprintf ppf "@\n%a," pe x; pp_v_list pe ppf xs

let pp_int f x = fprintf f "%d" x
let pp_string f x = fprintf f "%s" x
let pp_constant_as_int i f c = pp_int f (i.idx_constant.to_int c)
let pp_string_as_int i f s =
  let v = (match s with None -> (-1) | Some s -> i.idx_string.to_int s) in
  pp_int f v
let pp_list pe f x =
  fprintf f "@[<2>%d@ %a@]" (List.length x) (pp_list_sep " " pe) x
let pp_array pe f x = pp_list pe f (Array.to_list x)

let pp_value_guard index f = function
  | A.Variable (v, i) -> fprintf f "0 %d %d" i v
  | A.Constant (c, i) -> fprintf f "1 %d %a" i (pp_constant_as_int index) c

let pp_pattern tags f p =
  fprintf f "%a" (pp_list pp_int) (Hashtbl.find tags p)

let pp_condition index = pp_list (pp_value_guard index)

let pp_assignment f (x, i) =
  fprintf f "%d %d" x i

let pp_guard tags index f { A.tag_guard = p; A.value_guards = cs } =
  fprintf f "%a %a" (pp_pattern tags) p (pp_condition index) cs

let pp_action = pp_list pp_assignment

let pp_step tags index f { A.guard = g; A.action = a } =
  fprintf f "%a %a" (pp_guard tags index) g pp_action a

let pp_transition tags index f { steps = ss; target = t } =
  fprintf f "%a %d" (pp_list (pp_step tags index)) ss t

let pp_vertex tags index f v =
  fprintf f "%a %a"
    (pp_string_as_int index) (Some v.vertex_name)
    (pp_list (pp_transition tags index)) v.outgoing_transitions

let list_of_hash h =
  let r = ref [] in
  for i = Hashtbl.length h - 1 downto 0 do
    r := (try Some (Hashtbl.find h i) with Not_found -> None) :: !r
  done;
  !r

let pp_automaton index f x =
  let obs_p p = Hashtbl.find x.pattern_tags (Hashtbl.find x.observables p) in
  let iop = to_ints (get_properties x) in
  let poi = inverse_index (fun x -> x) iop in
  let pov =
    Array.map (fun v -> Hashtbl.find iop v.vertex_property) x.vertices in
  let obs_tags = Array.to_list (Array.map obs_p poi) in
  fprintf f "%a@\n" (pp_list pp_int) (starts x);
  fprintf f "%a@\n" (pp_list (pp_string_as_int index)) (errors x);
  fprintf f "%a@\n" (pp_array (pp_vertex x.pattern_tags index)) x.vertices;
  fprintf f "%a@\n" (pp_array pp_int) pov;
  fprintf f "%a@\n" (pp_list (pp_list pp_int)) obs_tags;
  fprintf f "%a@\n"
    (pp_list (pp_string_as_int index)) (list_of_hash x.event_names)

let mk_pp_index p =
  let mk () =
    let m = Hashtbl.create 0 in
    let c = ref (-1) in
    let add x = if not (Hashtbl.mem m x) then Hashtbl.add m x (incr c; !c) in
    add, m, c in
  let mk_idx m c =
    { to_int = Hashtbl.find m
    ; of_int = (let a = inverse_index (fun x -> x) m in fun i -> a.(i))
    ; count = succ !c } in
  let add_c, ioc, cc = mk () in
  let add_s, ios, sc = mk () in
  let value_guard = function A.Constant (c, _) -> add_c c | _ -> () in
  let event_guard g = List.iter value_guard g.A.value_guards in
  let label l = event_guard l.A.guard in
  let transition t = List.iter label t.steps in
  let vertex_data v =
    add_s v.vertex_name; List.iter transition v.outgoing_transitions in
  Array.iter vertex_data p.vertices;
  Hashtbl.fold (fun _ en () -> add_s en) p.event_names ();
  List.iter (function None -> () | Some s -> add_s s) (errors p);
  { idx_constant = mk_idx ioc cc
  ; idx_string = mk_idx ios sc }

let pp_constants_table j i =
  let constants =
    let rec ct n =
      if n = i.idx_constant.count
      then []
      else i.idx_constant.of_int n :: ct (succ n) in
    ct 0 in
  let pp_ext f e =
    fprintf f "@[\"topl\"@ + java.io.File.separator@ + \"Property.%s\"@]" e in
  fprintf j "@[";
  fprintf j "package topl;@\n";
  fprintf j "@[<2>public class Property {";
  fprintf j "@\n@[<2>public static final Object[] constants =@ ";
  fprintf j   "new Object[]{%a@]};" (pp_v_list pp_string) constants;
  fprintf j "@\npublic static Checker checker = null;";
  fprintf j "@\n@[<2>public static void check(Checker.Event event) {";
  fprintf j   "@\n@[<2>if (checker != null) {";
  fprintf j     "@\nchecker.check(event);";
  fprintf j   "@]@\n}";
  fprintf j "@]@\n}";
  fprintf j "@\n@[<2>public static void start() {";
  fprintf j   "@\n@[<2>if (checker == null) {";
  fprintf j     "@\n@[<2>checker =@ Checker.Parser.checker(%a,@ %a,@ constants);@]" pp_ext "text"  pp_ext "strings";
  fprintf j   "@\nchecker.historyLength = 10;";
  fprintf j   "@\nchecker.statesLimit = 10;";
  fprintf j   "@\nchecker.captureCallStacks = false;";
  fprintf j   "@\nchecker.selectionStrategy = Checker.SelectionStrategy.NEWEST;";
  fprintf j   "@]@\n}";
  fprintf j "@]@\n}";
  fprintf j "@\n@[<2>public static void stop() {";
  fprintf j   "@\nchecker = null;";
  fprintf j "@]@\n}";
  fprintf j "@]@\n}@]"

let pp_strings_nonl f index =
  for i = 0 to pred index.idx_string.count do
    let s = index.idx_string.of_int i in
    assert (not (String.contains s '\n'));
    Printf.fprintf f "%s\n" s
  done

let generate_checkers out_dir p =
  failwith "XXX"
  (*
  check_automaton p;
  let (/) = Filename.concat in
  U.cp_r (Config.topl_dir/"src"/"topl") out_dir;
  let topl_dir = out_dir/"topl" in
  let o n =
    let c = open_out (topl_dir/("Property." ^ n)) in
    let f = formatter_of_out_channel c in
    (c, f) in
  let (jc, j), (tc, t) = o "java", o "text" in
  let sc = open_out (topl_dir/"Property.strings") in
  let index = mk_pp_index p in
  fprintf j "@[%a@." pp_constants_table index;
  pp_strings_nonl sc index;
  fprintf t "@[%a@." (pp_automaton index) p;
  List.iter close_out_noerr [jc; tc; sc];
  ignore (Sys.command
    (Printf.sprintf
      "javac -sourcepath %s %s"
      (U.command_escape out_dir)
      (U.command_escape (topl_dir/"Property.java")))) *)

(* }}} *)
(* conversion to Java representation *) (* {{{ *)

let index_for_var ifv v =
  try
    Hashtbl.find ifv v
  with Not_found ->
    let i = Hashtbl.length ifv in
      Hashtbl.replace ifv v i; i

let transform_tag_guard ptags tg =
  Hashtbl.replace ptags tg []; tg

let transform_value_guard ifv = function
  | A.Variable (v, i) -> A.Variable (index_for_var ifv v, i)
  | A.Constant (c, i) -> A.Constant (c, i)

let transform_guard ifv ptags {A.tag_guard=tg; A.value_guards=vgs} =
  { A.tag_guard = transform_tag_guard ptags tg
  ; A.value_guards = List.map (transform_value_guard ifv) vgs }

let transform_condition ifv (store_var, event_index) =
  let store_index = index_for_var ifv store_var in
    (store_index, event_index)

let transform_action ifv a = List.map (transform_condition ifv) a

let transform_label ifv ptags {A.guard=g; A.action=a} =
  { A.guard = transform_guard ifv ptags g
  ; A.action = transform_action ifv a }

let transform_properties ps =
  let vs p = p |> get_vertices |> List.map (fun v -> (p, v)) in
  let iov = to_ints (ps >>= vs) in
  let mk_vd (p, v) =
    { vertex_property = p
    ; vertex_name = v
    ; outgoing_transitions = [] } in
  let full_p =
    { vertices = inverse_index mk_vd iov
    ; observables = Hashtbl.create 0
    ; pattern_tags = Hashtbl.create 0
    ; event_names = Hashtbl.create 0 } in
  let add_obs_tags p =
    let obs_tag =
      { A.event_type = None
      ; A.method_name = p.A.observable
      ; A.method_arity = (0, None) } in
    Hashtbl.replace full_p.pattern_tags obs_tag [];
    Hashtbl.replace full_p.observables p obs_tag in
  List.iter add_obs_tags ps;
  let add_transition vi t =
    let vs = full_p.vertices in
    let ts = vs.(vi).outgoing_transitions in
    vs.(vi) <- { vs.(vi) with outgoing_transitions = t :: ts } in
  let ifv = Hashtbl.create 0 in (* variable, string -> integer *)
  let pe p {A.source=s;A.target=t;A.labels=ls} =
    let s = Hashtbl.find iov (p, s) in
    let t = Hashtbl.find iov (p, t) in
    let ls = List.map (transform_label ifv full_p.pattern_tags) ls in
    add_transition s {steps=ls; target=t} in
  List.iter (fun p -> List.iter (pe p) p.A.transitions) ps;
  full_p

(* }}} *)
(* bytecode instrumentation *) (* {{{ *)

let does_method_match
  ({ method_name=mn; method_arity=ma }, mt)
  { A.event_type=t; A.method_name=re; A.method_arity=(amin, amax) }
=
  let bamin = amin <= ma in
  let bamax = option true ((<=) ma) amax in
  let bt = option true ((=) mt) t in
  let bn = A.pattern_matches re mn in
  let r = bamin && bamax  && bt && bn in
  if log log_mm then begin
    printf "@\n@[<2>%s " (if r then "✓" else "✗");
    printf "(%a, %s, %d)@ matches (%a, %s, [%d..%a])@ gives (%b, %b, (%b,%b))@]"
      A.pp_event_type mt mn ma
      (pp_option A.pp_event_type) t
      re.A.p_string
      amin
      (pp_option pp_int) amax
      bt bn bamin bamax
  end;
  r

let get_tag x =
  let cnt = ref (-1) in
  fun t (mns, ma) mn ->
    let en = (* event name *)
      fprintf str_formatter "%a %s" A.pp_event_type t mn;
      flush_str_formatter () in
    let fp p acc =
      let cm mn = does_method_match ({method_name=mn; method_arity=ma}, t) p in
      if List.exists cm mns then p :: acc else acc in
    let fpk p _ = fp p in
    let fpv _ = fp in
    if Hashtbl.fold fpv x.observables [] <> [] then begin
      match Hashtbl.fold fpk x.pattern_tags [] with
        | [] -> None
        | ps ->
            incr cnt;
            let at p =
              let ts = Hashtbl.find x.pattern_tags p in
              (* printf "added tag %d\n" !cnt; *)
              Hashtbl.replace x.pattern_tags p (!cnt :: ts);
              Hashtbl.replace x.event_names !cnt en in
            List.iter at ps;
            Some !cnt
    end else None

let get_ancestors h c =
  let cs = Hashtbl.create 0 in
  let rec ga c =
    if not (Hashtbl.mem cs c) then begin
      Hashtbl.add cs c ();
      let parents = try Hashtbl.find h c with Not_found -> [] in
      List.iter ga parents
    end in
  ga c;
  Hashtbl.fold (fun c _ cs -> c :: cs) cs []

let mk_full_method_name c mn = failwith "XXX"
(*  name_of_class c ^ "." ^ mn *)

let get_overrides h c m =
  let ancestors = get_ancestors h c in
  let qualify c =  mk_full_method_name c m.method_name in
  (List.map qualify ancestors, m.method_arity)

let compute_inheritance in_dir = failwith "XXX"
(*
  let h = Hashtbl.create 0 in
  let record_class c =
    let parents = match c.BH.c_extends with
      | None -> c.BH.c_implements
      | Some e -> e :: c.BH.c_implements in
    Hashtbl.replace h c.BH.c_name parents in
  ClassMapper.iter in_dir record_class;
  h
  *)

(* }}} *)
(* main *) (* {{{ *)

let read_properties fs =
  fs |> List.map Topl.Helper.parse >>= List.map (fun x -> x.A.ast)

(*
  printf "@[";
  let usage = Printf.sprintf
    "usage: %s -i <dir> [-o <dir>] <topls>" Sys.argv.(0) in
  try
    let fs = ref [] in
    let in_dir = ref None in
    let out_dir = ref None in
    let set_dir r v = match !r with
      | Some _ -> raise (Arg.Bad "Repeated argument.")
      | None -> r := Some v in
    Arg.parse
      [ "-i", Arg.String (set_dir in_dir), "input directory"
      ; "-o", Arg.String (set_dir out_dir), "output directory" ]
      (fun x -> fs := x :: !fs)
      usage;
    if !in_dir = None then begin
      eprintf "@[Missing input directory.@\n%s@." usage;
      exit 2;
    end;
    if !out_dir = None then out_dir := !in_dir;
    let in_dir, out_dir = U.from_some !in_dir, U.from_some !out_dir in
    let tmp_dir = U.temp_path "toplc_" in
    List.iter check_work_directory [in_dir; out_dir; tmp_dir];
    let ps = read_properties !fs in
    let h = compute_inheritance in_dir in
    let p = transform_properties ps in
    ClassMapper.map in_dir tmp_dir (instrument_class (get_tag p) h);
    generate_checkers tmp_dir p;
    U.rm_r out_dir;
    U.rename tmp_dir out_dir;
    printf "@."
  with
    | Helper.Parsing_failed m
    | Sys_error m
        -> eprintf "@[ERROR: %s@." m
*)
(* }}} *)
