(********************************************************
   This file is part of jStar
        src/jimple_syntax/pprinter.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Pretty printer module *)

open Corestar_std
open Format

(* TODO(rgrig): Don't open these modules. *)
open Jparsetree
open Jimple_global_types

module J = Jparsetree
(* module PS = Psyntax *)

(* TODO(rgrig): The functions here should be pretty printers. *)

let binop2str bo =
  match bo with
  | And -> "&"
  | Or -> "|"
  | Xor -> "^"
  | Mod -> "%"
  | Cmp -> "cmp"
  | Cmpg -> "cmpg"
  | Cmpl -> "cmpl"
  | Cmpeq -> "=="
  | Cmpne -> "!="
  | Cmpgt -> ">"
  | Cmpge -> ">="
  | Cmplt -> "<"
  | Cmple -> "<="
  | Shl -> "<<"
  | Shr -> ">>"
  | Ushr -> ">>>"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div  -> "/"

let unop2str uo =
  match uo with
  |Lengthof -> "lengthof"
  | Neg -> "new"

let nonstatic_invoke2str i =
  match i with
  | Special_invoke -> "specialinvoke"
  | Virtual_invoke ->  "virtualinvoke"
  | Interface_invoke -> "interfaceinvoke"


let identifier2str i = i
let at_identifier2str i = i
let quoted_name2str i  = i
let full_identifier2str i = i
let array_brackets2str i = i

let label_name2str =  identifier2str

let name2str = string_of J.pp_name

let class_name2str = string_of J.pp_class_name

let immediate2str = string_of Expression.pp

let fixed_array_descriptor2str s = "["^immediate2str s^"]"

let array_descriptor2str = function
  | Some i -> immediate2str i
  | None -> ""

let j_file_type2str = function
  | ClassFile -> "class"
  | InterfaceFile -> "interface"

let  modifier2str = function
   | Abstract ->"abstract"
   | Final ->"final"
   | Native ->"native"
   | Public ->"public"
   | Protected ->"protected"
   | Private ->"private"
   | Jparsetree.Static ->"static"
   | Synchronized ->"synchronized"
   | Transient ->"transient"
   | Volatile ->"volatile"
   | Strictfp ->"strictfp"
   | Enum ->"enum"
   | Annotation ->"annotation"

let j_base_type2str = function
  | Boolean -> "boolean"
  | Byte -> "byte"
  | Char -> "char"
  | Short -> "short"
  | Int -> "int"
  | Long -> "long"
  | Float -> "float"
  | Double -> "double"
  | Null_type  -> "null_type"
  | Class_name n -> class_name2str n

(* takse some list l of some whatever type and a function f to transform this type in string,
a separator between element and return a string containing every element *)
let rec list2str f l sep=
  match l with
  | [] -> ""
  | [s] -> f s
  | s::tail -> (f s) ^sep^ (list2str f tail sep )

let list_option2list lso =
  match lso with
  | None    -> []
  | Some ls -> ls


let nonvoid_type2str =function
  | Base (b,al) ->  j_base_type2str b ^ (list2str array_brackets2str al "")
  | Quoted (qn,al) ->  quoted_name2str qn ^ (list2str array_brackets2str al "")
  | Ident_NVT (i,al) ->   identifier2str i ^ (list2str array_brackets2str al "")
  | Full_ident_NVT (i,al) -> full_identifier2str i ^ (list2str array_brackets2str al "")

let parameter2str p =  nonvoid_type2str p

let  j_type2str = function
  | Void -> "void"
  | Non_void t -> nonvoid_type2str t

let throws_clause2str = function
  | Some c -> "throws "^(list2str class_name2str c ", ")
  | None -> ""

let case_label2str = function
  | Case_label_default -> "default"
  | Case_label s ->"case "^s

let mkStrOfFieldSignature c t n=
  "<"^class_name2str c ^": "^ j_type2str t ^" "^name2str n^">"

let declaration2str = function
  | Declaration (Some t,nl) -> j_type2str t ^  (list2str name2str  nl ", ")^";"
  | Declaration (None,nl) -> (list2str name2str  nl ", ")^";"

let case_statement2str = function
  | Case_stmt (cl,ln) -> case_label2str cl ^": goto "^label_name2str ln

let signature2str = function
  | Method_signature (c,t,n,pl) -> "<"^class_name2str c ^": "^ j_type2str t ^" "^ name2str n
      ^"("^  (list2str parameter2str pl ", " )^")>"
  | Field_signature (c,t,n) ->  mkStrOfFieldSignature c t n

let reference2str = function
  |Array_ref (id,im) ->  identifier2str id ^ fixed_array_descriptor2str im
  |Field_local_ref (n,s) ->  name2str n ^"."^  signature2str s
  |Field_sig_ref s ->  signature2str s

let variable2str = function
  | Var_ref r -> reference2str r
  | Var_name n -> name2str n

let invoke_expr2str = function
 | Invoke_nostatic_exp(i,n,s,il) ->
     nonstatic_invoke2str i ^" "^ name2str n ^"."^signature2str s ^"("^
   (list2str immediate2str il ", ")^")"
 | Invoke_static_exp(s,il)-> "staticinvoke " ^ signature2str s ^"("^ (list2str immediate2str il ", ") ^ ")"


let expression2str = function
  | New_simple_exp t -> "new "^j_base_type2str t
  | New_array_exp (t,a) -> "newarray["^nonvoid_type2str t ^"]"^ fixed_array_descriptor2str a
  | New_multiarray_exp (t,a) -> "newmultiarray["^j_base_type2str t ^"]"^ (list2str array_descriptor2str a "")
  | Cast_exp (t,i) -> "("^nonvoid_type2str t ^")"^ immediate2str i
  | Instanceof_exp (i,t) -> immediate2str i ^"instanceof "^nonvoid_type2str t
  | Binop_exp (bo,i1,i2) ->   immediate2str i1 ^" "^binop2str bo^" "^immediate2str i2
  | Unop_exp (uo,i) -> unop2str uo  ^" "^  immediate2str i
  | Invoke_exp e -> invoke_expr2str e
  | Immediate_exp e -> immediate2str e
  | Reference_exp e -> reference2str e

let statement2str = function
   | Label_stmt l ->  label_name2str l ^":"
   | Breakpoint_stmt -> "breakpoint"
   | Entermonitor_stmt i ->  "entermonitor "^ immediate2str i^";"
   | Exitmonitor_stmt i ->   "exitmonitor "^ immediate2str i^";"
   | Tableswitch_stmt (i,cl) ->
       "tableswitch("^immediate2str i ^"){"^ (list2str  case_statement2str cl ", ")^"};"
   | Lookupswitch_stmt(i,cl) ->
       "lookupswitch("^immediate2str i ^"){"^ (list2str  case_statement2str cl ", ")^"};"
   | Identity_stmt(n,i,t) -> name2str n ^" := "^ at_identifier2str i ^" "^ j_type2str t ^";"
   | Identity_no_type_stmt(n,i) -> name2str n ^" := "^ at_identifier2str i ^";"
   | Assign_stmt (v,e)-> variable2str v ^" = "^ expression2str e ^";"
   | If_stmt (e,l) -> "if "^ expression2str e ^" goto "^ label_name2str l
   | Goto_stmt l ->"goto "^list2str label_name2str l ", "^";"
   | Nop_stmt -> "nop;"
   | Ret_stmt(Some i) -> "ret "^immediate2str i^";"
   | Ret_stmt(None) -> "ret;"
   | Return_stmt (Some i) -> "return "^immediate2str i^";"
   | Return_stmt (None) -> "return;"
   | Throw_stmt i -> "throw "^immediate2str i^";"
   | Invoke_stmt e -> invoke_expr2str e^";"
   | Spec_stmt asgn -> string_of CoreOps.pp_statement (Core.Assignment_core asgn)

let declaration_or_statement2str =function
  |  DOS_dec d -> declaration2str d
  |  DOS_stm (s,_) -> statement2str s

let pp_catch_clause f { J.catch_exception; catch_from; catch_to; catch_with } =
  fprintf f "catch %s from %s to %s with %s;"
    (class_name2str catch_exception)
    (label_name2str catch_from)
    (label_name2str catch_to)
    (label_name2str catch_with)

let method_body2str = function
  |None -> ";"
  |Some (dl,cl) ->
      let cs = string_of (pp_list_sep ", " pp_catch_clause) cl in
     "\n{"^(list2str declaration_or_statement2str dl "\n")^" "^cs^"\n}"

let old_clauses2str ocs = List.fold_left (fun acc oc -> acc^"old "^ method_body2str oc^"\n") "" ocs

let member2str = function
  | Field(ml,j,n) -> (list2str modifier2str ml " ")^" "^ j_type2str j ^" "^name2str n^";"
  | Method(ml,j,n,pl,tc,rc,ocs,ec,mb) ->
      (list2str modifier2str ml " ") ^" "^  j_type2str j ^" "^ name2str n ^"("^
	(list2str parameter2str pl ", ")^") "^throws_clause2str tc
        ^"\nrequires"^ method_body2str rc ^"\n"^ old_clauses2str ocs ^"ensures"^
        method_body2str ec ^"\n"^ method_body2str mb

let extends_clause2str = function
  |[] -> ""
  |cl -> "extends "^(list2str class_name2str cl " ")

let implements_clause2str = function
  | [] -> ""
  | cl -> "implements "^(list2str class_name2str cl " ")

let jimple_file2str = function
  | JFile (ml,j,c,e,i,meml) ->
      (list2str modifier2str ml " ")^ j_file_type2str j ^" "^
	class_name2str c  ^" "^extends_clause2str e ^" "^ implements_clause2str i
      ^"\n{\n"^ (list2str member2str meml "\n\n")^"\n}"



