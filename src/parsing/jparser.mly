/********************************************************
   This file is part of jStar
	src/parsing/jparser.mly
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************/
/* ddino implementation of a parser for Jimple */

%{ (* header *)
exception Give_up

open Corestar_std
open Format

open Jparsetree

(* TODO(rgrig): Don't open these. *)
open Core
open Jimple_global_types
open Lexing
open Load
open Parsing
open Printing
open Spec_def

(* TODO(rgrig): Keep these instead of the above. *)
module J = Jparsetree
module SS = Support_syntax
module U = Untyped

let newVar x =
  if x = "_" then
    Syntax.freshen (U.mk_lvar "v")
  else if String.get x 0 = '_' then
    U.mk_lvar (String.sub x 1 (String.length x -1 ))
  else
    U.mk_plvar x

(* let check_npv =                                *)
(*   let rec check_term_npv =  failwith "TODO" in *)
    (* function                                                                   *)
    (* | Arg_var v ->                                                             *)
    (*     if Vars.is_avar v then begin                                           *)
    (*       eprintf "@[@{<b>ERROR@}: You can't use pattern %a in this context@." *)
    (*         Vars.pp_var v;                                                     *)
    (*       raise Parsing.Parse_error                                            *)
    (*     end                                                                    *)
    (* | Arg_string _ -> ()                                                       *)
    (* | Arg_op (_, xs) -> List.iter check_term_npv xs                            *)
    (* | _ -> failwith "INTERNAL: Using deprecated stuff." in                     *)
  (* let check_term_list_npv = List.iter check_term_npv in *)
  (* let rec check_pform_at_npv =  failwith "TODO"         *)
    (* function                                           *)
    (* | P_EQ (t1, t2)                                    *)
    (* | P_NEQ (t1, t2) -> check_term_list_npv [t1; t2]   *)
    (* | P_PPred (_, ts)                                  *)
    (* | P_SPred (_, ts) -> check_term_list_npv ts        *)
    (* | P_Wand (f1, f2)                                  *)
    (* | P_Or (f1, f2)                                    *)
    (* | P_Septract (f1, f2) -> check_pform_npv (f1 @ f2) *)
    (* | P_False -> ()                                    *)
  (* and check_pform_npv f = List.iter check_pform_at_npv f in *)
  (* check_pform_npv                                           *)

let msig_simp (mods,typ,name,args_list) =
  let args_list = List.map fst args_list in
  (mods,typ,name,args_list)

let bind_spec_vars (mods,typ,name,args_list) triple = triple
  (* TODO: What is below should be reimplemented to allow users to use
  friendlier identifiers in specs (rather than the funny-looking jimple-ones). *)
  (* (* Make substitution to normalise names *)                                                 *)
  (* let subst = Psyntax.empty in                                                               *)
  (* let subst = Psyntax.add (concretep_str "this") (Arg_var(Support_syntax.this_var)) subst in *)
  (* (* For each name that is given convert to normalised param name. *)                        *)
  (* let _, subst =                                                                             *)
  (*   List.fold_left                                                                           *)
  (*     (fun (n,subst) arg_opt ->                                                              *)
	(* (n+1,                                                                                      *)
	(*  match arg_opt with                                                                        *)
	(*    ty,None -> subst                                                                        *)
	(*  | ty,Some str ->                                                                          *)
	(*      Psyntax.add                                                                           *)
	(*        (concretep_str str)                                                                 *)
	(*        (Arg_var(Support_syntax.parameter_var n))                                           *)
	(*        subst                                                                               *)
	(* ))                                                                                         *)
	(*   (0,subst) args_list in                                                                   *)
  (* Specification.sub_triple subst triple                                                      *)

let mkDynamic (msig, specs, source_pos) =
  let specs = List.map (bind_spec_vars msig) specs in
  let msig = msig_simp msig in
  Dynamic(msig, specs, source_pos)

let mkStatic (msig, specs, source_pos) =
  let specs = List.map (bind_spec_vars msig) specs in
  let msig = msig_simp msig in
  Static(msig, specs, source_pos)


let location_to_string pos =
  Printf.sprintf "Line %d character %d" pos.pos_lnum  (pos.pos_cnum - pos.pos_bol + 1)

let parse_error s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Error between %s and %s\n%s\n" (location_to_string start_pos) (location_to_string end_pos) s

let parse_warning s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Warning %s (between %s and %s)\n" s (location_to_string start_pos) (location_to_string end_pos)

let field_signature2str fs =
  match fs with
  | Field_signature (c,t,n) ->  Pprinter.mkStrOfFieldSignature c t n
  | _ -> assert false


%} /* declarations */

/* ============================================================= */
/* tokens */
%token ABDUCTION
%token ABS
%token ABSTRACT
%token AND
%token ANDALSO
%token ANNOTATION
%token AS
%token AT_IDENTIFIER
%token AXIOMS
%token BANG
%token BIMP
%token BOOLEAN
%token BREAKPOINT
%token BYTE
%token CASE
%token CATCH
%token CHAR
%token CLASS
%token CMP
%token CMPEQ
%token CMPG
%token CMPGE
%token CMPGT
%token CMPL
%token CMPLE
%token CMPLT
%token CMPNE
%token COLON
%token COLON_EQUALS
%token COMMA
%token DEFAULT
%token DEFINE
%token DIV
%token DOT
%token DOUBLE
%token EMP
%token ENSURES
%token ENTERMONITOR
%token ENUM
%token EOF
%token EQUALS
%token EXITMONITOR
%token EXPORT
%token EXPORTS
%token EXTENDS
%token FALSE
%token FINAL
%token FLOAT
%token FLOAT_CONSTANT
%token FRAME
%token FROM
%token FULL_IDENTIFIER
%token GOTO
%token IDENTIFIER
%token IF
%token IMP
%token IMPLEMENTS
%token IMPLICATION
%token IMPORT
%token INCONSISTENCY
%token INSTANCEOF
%token INT
%token INTEGER_CONSTANT
%token INTERFACE
%token INTERFACEINVOKE
%token L_BRACE
%token L_BRACKET
%token LENGTHOF
%token LONG
%token LOOKUPSWITCH
%token L_PAREN
%token MAPSTO
%token MINUS
%token MOD
%token MULT
%token NATIVE
%token NEG
%token NEW
%token NEWARRAY
%token NEWMULTIARRAY
%token NOP
%token NULL
%token NULL_TYPE
%token OLD
%token OR
%token OROR
%token PLUS
%token PRIVATE
%token PROTECTED
%token PUBLIC
%token QUESTIONMARK
%token QUOTED_NAME
%token R_BRACE
%token R_BRACKET
%token REQUIRES
%token RET
%token RETURN
%token R_PAREN
%token SEMICOLON
%token SHL
%token SHORT
%token SHR
%token SOURCE_POS_TAG
%token SOURCE_POS_TAG_CLOSE
%token SPEC
%token SPECIALINVOKE
%token STATIC
%token STATICINVOKE
%token STRICTFP
%token STRING_CONSTANT
%token SYNCHRONIZED
%token TABLESWITCH
%token THROW
%token THROWS
%token TO
%token TRANSIENT
%token UNKNOWN
%token USHR
%token VDASH
%token VIRTUALINVOKE
%token VOID
%token VOLATILE
%token WHERE
%token WITH
%token XOR

%type <string> FLOAT_CONSTANT
%type <string> INTEGER_CONSTANT
%type <string> AT_IDENTIFIER
%type <string> FULL_IDENTIFIER
%type <string> IDENTIFIER
%type <string> QUOTED_NAME
%type <string> STRING_CONSTANT

%type <string> AT_IDENTIFIER
%type <string> FULL_IDENTIFIER
%type <string> IDENTIFIER
%type <string> QUOTED_NAME
%type <string> STRING_CONSTANT


/* === associativity and precedence === */

%left IDENTIFIER
%left AT_IDENTIFIER
%left QUOTED_NAME
%left FULL_IDENTIFIER

%left OR
%left OROR
%left MULT
%left AND
%left XOR
%left MOD
%left CMP
%left CMPG
%left CMPL
%left CMPEQ
%left CMPNE
%left CMPGT
%left CMPGE
%left CMPLT
%left CMPLE
%left SHL
%left SHR
%left USHR
%left PLUS
%left MINUS
%left DIV


/* entry points */
//%start listing_file
//%type <Jparsetree.list_class_file> listing_file
%start file
%type <Jimple_global_types.jimple_file> file

%start spec_file
%type <Spec_def.class_spec Load.entry list> spec_file

%start triple
%type <Core.triple> triple

%start jargument     /* used for parsing topl values */
%type <Z3.Expr.expr> jargument

%% /* rules */



file:
   | modifier_list_star file_type class_name extends_clause implements_clause file_body
       {JFile($1, $2, $3, $4, $5, $6)}
;

spec_file:
   | EOF  { [] }
   | IMPORT  STRING_CONSTANT  SEMICOLON spec_file{ (ImportEntry $2) :: $4 }
   | classspec spec_file { (NormalEntry $1) :: $2 }

classspec:
  | file_type class_name extends_clause implements_clause L_BRACE
      apf_defines
      exports_clause
      axioms_clause
      methods_specs
    R_BRACE
      { { class_or_interface = $1
        ; classname = $2
        ; extends = $3
        ; implements = $4
        ; apf = $6
        ; exports = $7
        ; axioms = $8
        ; methodspecs = $9} }


apf_defines:
   | apf_define apf_defines { $1 :: $2 }
   | /*empty*/ { [] }

apf_define:
   | EXPORT identifier L_PAREN lvariable paramlist_question_mark R_PAREN AS formula SEMICOLON
       { let a=match $5 with | Some b -> b | None -> [] in ($2,$4,a,$8,true) }
   | DEFINE identifier L_PAREN lvariable paramlist_question_mark R_PAREN AS formula SEMICOLON
       { let a=match $5 with | Some b -> b | None -> [] in ($2,$4,a,$8,false) }

exports_clause:
  | EXPORTS L_BRACE named_implication_star R_BRACE WHERE L_BRACE exportLocal_predicate_def_star R_BRACE { Some ($3,$7) }
  | /*empty*/ {None}

axioms_clause:
  | AXIOMS L_BRACE named_implication_star R_BRACE { Some $3 }
  | /*empty*/ {None}

named_implication_star:
  | named_implication named_implication_star { $1 @ $2 }
  | /*empty*/ { [] }

named_implication:
   | identifier COLON formula IMP formula SEMICOLON { [($1,$3,$5)] }
   | identifier COLON formula BIMP formula SEMICOLON { [($1^"_forwards",$3,$5); ($1^"_backwards",$5,$3)] }

exportLocal_predicate_def_star:
   | exportLocal_predicate_def exportLocal_predicate_def_star { $1 :: $2 }
   | /*empty*/ { [] }

exportLocal_predicate_def:
   | identifier L_PAREN lvariable_list_ne R_PAREN AS formula SEMICOLON
      { ($1,$3,$6) }

methods_specs:
   | SPEC method_spec methods_specs { $2 :: $3 }
   | /*empty*/ { [] }
;

modifies:
  | /* empty */ { [] }
  | L_PAREN lvariable_list R_PAREN { $2 }
;

triple:
  | L_BRACE formula R_BRACE modifies L_BRACE formula R_BRACE
    { { Core.pre = $2
      ; modifies = $4
      ; post = $6
      ; in_vars = failwith "92unf923"
      ; out_vars = failwith "d92wnb39" } }
;

specs:
   | triple ANDALSO specs  { $1 :: $3 }
   | triple  {[$1]}

method_spec:
   | method_signature_short COLON specs  SEMICOLON source_pos_tag_option { mkDynamic($1, $3, $5) }
   | method_signature_short STATIC COLON specs SEMICOLON source_pos_tag_option { mkStatic($1, $4, $6) }
   | method_signature_short COLON specs source_pos_tag_option { mkDynamic($1, $3, $4) }
   | method_signature_short STATIC COLON specs source_pos_tag_option { mkStatic($1, $4, $5) }

modifier:
   | ABSTRACT      {Abstract}
   | FINAL         {Final}
   | NATIVE        {Native}
   | PUBLIC        {Public}
   | PROTECTED     {Protected}
   | PRIVATE       {Private}
   | STATIC        {J.Static}
   | SYNCHRONIZED  {Synchronized}
   | TRANSIENT     {Transient}
   | VOLATILE      {Volatile}
   | STRICTFP      {Strictfp}
   | ENUM          {Enum}
   | ANNOTATION    {Annotation}
;
file_type:
   | CLASS  { ClassFile }
   | INTERFACE { InterfaceFile }

extends_clause:
   | EXTENDS class_name_list { $2 } /* stephan mult inh */
   | /* empty */ { [] }
;
implements_clause:
   | IMPLEMENTS class_name_list { $2 }
   | /* empty */ { [] }
;
file_body:
   | L_BRACE member_list_star R_BRACE {$2}
;
class_name_list:
   | class_name { [$1] }
   | class_name COMMA class_name_list {$1::$3}
;
modifier_list_star:
   | /* empty */ { [] }
   | modifier  modifier_list_star {$1::$2}
;
member_list_star:
   | /* empty */ { [] }
   | member  member_list_star {$1::$2}
;
member:
   | modifier_list_star jtype name SEMICOLON {Field($1,$2,$3)}
   | modifier_list_star jtype name L_PAREN parameter_list_question_mark R_PAREN
   throws_clause requires_clause old_clauses ensures_clause method_body
   {Method($1,$2,$3,$5,$7,$8,$9,$10,$11)}
;
jtype:
   | VOID {Void}
   | nonvoid_type {Non_void($1)}
;
parameter_list:
   | parameter { [$1] }
   | parameter COMMA parameter_list { $1::$3 }
;
parameter_list_args_opt:
   | parameter_args_opt { [$1] }
   | parameter_args_opt COMMA parameter_list_args_opt { $1::$3 }
;
parameter:
   | nonvoid_type {$1}
;
parameter_args_opt:
   | nonvoid_type {$1,None}
   | nonvoid_type identifier {$1,Some $2}
;
throws_clause:
   | THROWS class_name_list { Some $2 }
   | /* empty */ { None }
;
requires_clause:
   | REQUIRES method_body { $2 }
   | /* empty */ { None }
;
old_clauses:
   | old_clause old_clauses { $1::$2 }
   | /* empty */ { [] }
;
old_clause:
   | OLD method_body { $2 }
;
ensures_clause:
   | ENSURES method_body { $2 }
   | /* empty */ { None }
;
base_type_no_name:
   | BOOLEAN {Boolean}
   | BYTE {Byte}
   | CHAR {Char}
   | SHORT {Short}
   | INT {Int}
   | LONG {Long}
   | FLOAT {Float}
   | DOUBLE {Double}
   | NULL {Null_type}
;
base_type:
   | base_type_no_name {$1}
   | class_name {Class_name $1}
;
quoted_name:
   | QUOTED_NAME { $1 }
;
identifier:
  | AS { "as" }
  | EMP    { "Emp" }
  | EXPORT { "export" }
  | EXPORTS { "exports" }
  | IDENTIFIER { $1 }
  | REQUIRES { "requires" }
;
at_identifier:
   | AT_IDENTIFIER { $1 }
;
full_identifier:
   | FULL_IDENTIFIER { $1 }
;
nonvoid_type:
   | base_type_no_name array_brackets_list_star  {Base($1,$2)}
   | quoted_name array_brackets_list_star {Quoted($1,$2)}
   | identifier array_brackets_list_star {Ident_NVT($1,$2)}
   | full_identifier array_brackets_list_star {Full_ident_NVT($1,$2)}
;
/* ddino: dunno what to do with this array_brackets. this in any case does not
   type check
   TODO: Shouldn't this be an integer, rather than a list of "[]"s?
 */
array_brackets_list_star:
   | /* empty */ { [] }
   | L_BRACKET R_BRACKET array_brackets_list_star { "[]"::$3 }
;
method_body:
   | SEMICOLON {None}
   | L_BRACE declaration_or_statement_list_star catch_clause_list_star R_BRACE  {Some($2,$3)}
;
source_pos_tag:
  | SOURCE_POS_TAG
      COLON identifier
      COLON INTEGER_CONSTANT identifier
      COLON INTEGER_CONSTANT identifier
      COLON INTEGER_CONSTANT identifier
      COLON INTEGER_CONSTANT identifier
      COLON full_identifier
    SOURCE_POS_TAG_CLOSE
      { let i = int_of_string in
        { begin_line=i $5; begin_column=i $11; end_line=i $8; end_column=i $14} }
;
source_pos_tag_option:
   | /* empty */ { None }
   | source_pos_tag { Some($1) }
;
declaration_or_statement:
   | declaration { DOS_dec($1) }
   | statement source_pos_tag_option { DOS_stm($1, $2) }
;
declaration_or_statement_list_star:
   | /* empty */ { [] }
   | declaration_or_statement  declaration_or_statement_list_star {$1::$2}
;
declaration:
   | jimple_type local_name_list SEMICOLON {Declaration($1,$2)}
;
catch_clause_list_star:
   | /* empty */ { [] }
   | catch_clause  catch_clause_list_star {$1::$2}
;
jimple_type:
   | UNKNOWN {None}
   | nonvoid_type {Some(Non_void($1))}
   | NULL_TYPE {None}
;
local_name:
   | name {$1}
;
local_name_list:
   | local_name { [$1] }
   | local_name COMMA local_name_list { $1::$3 }
;
case_stmt_list_plus:
   | case_stmt { [$1] }
   | case_stmt case_stmt_list_plus { $1::$2 }
;
statement:
  | label_name COLON  {Label_stmt($1)}
  | BREAKPOINT SEMICOLON  {Breakpoint_stmt}
  | ENTERMONITOR immediate SEMICOLON {Entermonitor_stmt($2)}
  | EXITMONITOR immediate SEMICOLON  {Exitmonitor_stmt($2)}
  | TABLESWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Tableswitch_stmt($3,$6)}
  | LOOKUPSWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Lookupswitch_stmt($3,$6)}
  | local_name COLON_EQUALS at_identifier SEMICOLON {Identity_no_type_stmt($1,$3)}
  | local_name COLON_EQUALS at_identifier jtype SEMICOLON  {Identity_stmt($1,$3,$4)}
  | variable EQUALS expression SEMICOLON  {Assign_stmt($1,$3)}
  | IF bool_expr goto_stmt     {If_stmt($2,$3)}
  | goto_stmt {Goto_stmt [$1]}
  | NOP SEMICOLON     {Nop_stmt}
  | RET immediate_question_mark SEMICOLON     {Ret_stmt($2)}
  | RETURN immediate_question_mark SEMICOLON  {Return_stmt($2)}
  | THROW immediate SEMICOLON     {Throw_stmt($2)}
  | invoke_expr SEMICOLON     {Invoke_stmt($1)}
  | L_BRACE lvariable_list R_BRACE COLON triple SEMICOLON
    { Spec_stmt
      { Core.asgn_rets = $2
      ; asgn_args = []
      (* TODO: change spec -> specs in grammar?*)
      ; asgn_spec = Core.TripleSet.singleton $5 } }
;
immediate_question_mark:
   | immediate {Some $1}
   | /* empty */ { None }
;
label_name:
   |identifier {$1}
;
case_stmt:
   |case_label COLON goto_stmt {Case_stmt($1,$3)}
;
case_label:
   | CASE MINUS INTEGER_CONSTANT {Case_label ("-"^$3) }
   | CASE INTEGER_CONSTANT {Case_label $2 }
   | DEFAULT  {Case_label_default}
;
goto_stmt:
   | GOTO label_name SEMICOLON {$2}
;
catch_clause:
  | CATCH class_name FROM label_name TO label_name WITH label_name SEMICOLON
      { { J.catch_exception = $2
        ; catch_from = $4
        ; catch_to = $6
        ; catch_with = $8 } }
;
expression:
   | new_expr   {$1}
   | L_PAREN nonvoid_type R_PAREN immediate {Cast_exp($2,$4)}
   | immediate INSTANCEOF nonvoid_type  {Instanceof_exp($1,$3)}
   | invoke_expr     {Invoke_exp $1}
   | reference {Reference_exp $1}
   | binop_expr {$1}
   | unop_expr {$1}
   | immediate {Immediate_exp $1}
;
new_expr:
   | NEW base_type  {New_simple_exp($2)}
   | NEWARRAY L_PAREN  nonvoid_type R_PAREN  fixed_array_descriptor {New_array_exp($3,$5)}
   | NEWMULTIARRAY  L_PAREN base_type R_PAREN array_descriptor_list_plus  {New_multiarray_exp($3,$5)}
;
array_descriptor_list_plus:
   | array_descriptor { [$1] }
   | array_descriptor array_descriptor_list_plus { $1::$2 }
;
array_descriptor:
  L_BRACKET immediate_question_mark R_BRACKET { $2 }
;
variable:
   |reference {Var_ref($1)}
   |local_name {Var_name($1)}
;
bool_expr:
   |binop_expr     {$1}
   |unop_expr    {$1}
;
arg_list_question_mark:
   | arg_list { $1 }
   | /* empty */ { [] }
;
invoke_expr:
   |nonstatic_invoke local_name DOT method_signature L_PAREN arg_list_question_mark R_PAREN
       {Invoke_nostatic_exp($1,$2,$4,$6)}
   |STATICINVOKE method_signature L_PAREN  arg_list_question_mark R_PAREN
       {Invoke_static_exp($2,$4)}
;
binop_expr:
   |immediate binop immediate {Binop_exp($2,$1,$3)}
;
unop_expr:
   | unop immediate {Unop_exp($1,$2)}
;
nonstatic_invoke:
   | SPECIALINVOKE      {Special_invoke}
   | VIRTUALINVOKE      {Virtual_invoke}
   | INTERFACEINVOKE    {Interface_invoke}
;
parameter_list_question_mark:
   | parameter_list { $1 }
   | /* empty */ { [] }
;
parameter_args_opt_list_question_mark:
   | parameter_list_args_opt { $1 }
   | /* empty */ { [] }
;
method_signature:
   | CMPLT class_name COLON jtype name L_PAREN parameter_list_question_mark R_PAREN CMPGT
       {Method_signature($2,$4,$5,$7)}
;
method_signature_short:
   | modifier_list_star jtype name L_PAREN parameter_args_opt_list_question_mark R_PAREN
       { $1,$2,$3,$5 }
;
reference:
   | array_ref  {$1}
   | field_ref  {$1}
;
array_ref:
  identifier fixed_array_descriptor {Array_ref($1,$2)}
;
field_ref:
   | local_name DOT field_signature     { Field_local_ref($1,$3)}
   | field_signature {Field_sig_ref($1)}
;
field_signature:
    CMPLT class_name COLON jtype name CMPGT  {Field_signature($2,$4,$5)}
;
fixed_array_descriptor:
   L_BRACKET immediate R_BRACKET {$2}
;
arg_list:
   | immediate { [$1] }
   | immediate COMMA arg_list { $1 :: $3 }
;
immediate:
  | local_name { U.mk_plvar (string_of J.pp_name $1) }
  | constant { $1 }
;
constant:
  | INTEGER_CONSTANT { Syntax.mk_int_const $1 }
  | MINUS INTEGER_CONSTANT { SS.mk_1 J.Neg (Syntax.mk_int_const $2) }
  | FLOAT_CONSTANT  {  failwith "TODO6" (*PS.mkNumericConst $1*) }
  | MINUS FLOAT_CONSTANT  { SS.mk_1 J.Neg (Syntax.mk_int_const $2) }
  | STRING_CONSTANT {  Syntax.mk_string_const $1 }
  | CLASS STRING_CONSTANT {  U.mk_app "class_const" [Syntax.mk_string_const $2]  }
  | NULL { U.mk_app "nil" [] }
;
binop_no_mult:
   | AND {And}
   | OR  {Jparsetree.Or}
   | XOR {Xor}
   | MOD {Mod}
   | CMP {Cmp}
   | CMPG {Cmpg}
   | CMPL {Cmpl}
   | CMPEQ {Cmpeq}
   | CMPNE {Cmpne}
   | CMPGT {Cmpgt}
   | CMPGE {Cmpge}
   | CMPLT {Cmplt}
   | CMPLE {Cmple}
   | SHL {Shl}
   | SHR {Shr}
   | USHR {Ushr}
   | PLUS {Plus}
   | MINUS {Minus}
   | DIV {Div}
;
binop_val_no_multor:
   | AND {And}
   | XOR {Xor}
   | MOD {Mod}
   | SHL {Shl}
   | SHR {Shr}
   | USHR {Ushr}
   | PLUS {Plus}
   | MINUS {Minus}
   | DIV {Div}
//   | OR  {Jparsetree.Or}
;
binop_cmp:
   | CMP {Cmp}
   | CMPG {Cmpg}
   | CMPL {Cmpl}
   | CMPEQ {Cmpeq}
   | CMPNE {Cmpne}
   | CMPGT {Cmpgt}
   | CMPGE {Cmpge}
   | CMPLT {Cmplt}
   | CMPLE {Cmple}
;
binop:
   |  binop_no_mult { $1 }
   |  MULT { Mult }
unop:
   | LENGTHOF   {Lengthof}
   | NEG {Neg}
;
class_name:
   | quoted_name     {Quoted_clname $1}
   | identifier {Identifier_clname $1}
   | full_identifier {Full_identifier_clname $1}
;
name:
   | quoted_name {Quoted_name $1}
   | identifier {Identifier_name $1}
;


lvariable:
   | at_identifier { U.mk_plvar $1 }
   | identifier { newVar $1 }
   | QUESTIONMARK identifier { U.mk_tpat $2 }
;

lvariable_list_ne:
   |  lvariable    { [$1] }
   |  lvariable COMMA lvariable_list_ne  { $1 :: $3 }
;

lvariable_list:
   |  {[]}
   | lvariable_list_ne { $1 }
;

fldlist:
   | identifier EQUALS jargument { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS jargument SEMICOLON fldlist  { ($1,$3) :: $5 }
;

paramlist_question_mark:
   | COMMA L_BRACE paramlist R_BRACE { Some $3 }
   | COMMA paramlist { Some $2 }
   | /* empty */ { None }
;
paramlist:
   | identifier EQUALS lvariable {  failwith "TODO10" (*[($1,Arg_var $3)]*) }
   | /*empty*/ { [] }
   | identifier EQUALS lvariable SEMICOLON fldlist  {  failwith "TODO11" (*($1,Arg_var $3) :: $5*) }
;


jargument:
  | RETURN { U.mk_plvar U.return }
  | lvariable { $1 }
  | identifier L_PAREN jargument_list R_PAREN {  failwith "TODO13" (*Arg_op($1,$3)*) }
  | constant { $1 }
  | field_signature { Syntax.mk_string_const (field_signature2str $1) }
  | L_BRACE fldlist R_BRACE {  failwith "TODO15" (*mkArgRecord $2*) }
  | L_PAREN jargument binop_val_no_multor jargument R_PAREN {  failwith "TODO16" (*Arg_op(Support_syntax.bop_to_prover_arg $3, [$2;$4])*) }
  /* TODO(rgrig): Last branch is weird. */
;
jargument_list_ne:
   | jargument {$1::[]}
   | jargument COMMA jargument_list_ne { $1::$3 }
jargument_list:
   | /*empty*/  {[]}
   | jargument_list_ne {$1}
;
formula:
     /*empty*/  { Syntax.mk_emp }
   | EMP  { Syntax.mk_emp }
   | FALSE { Syntax.mk_false }
   | lvariable DOT jargument MAPSTO  jargument
     { U.mk_app "field" [$1; $3; $5] }
   | BANG identifier L_PAREN jargument_list R_PAREN
     { failwith "TODO18" (*[P_PPred($2, $4)]*) }
   | identifier L_PAREN jargument_list R_PAREN
     { failwith "TODO19"
      (*if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)]*) }
   | full_identifier L_PAREN jargument_list R_PAREN
     { failwith "TODO20"
      (*if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)]*) }
   | formula MULT formula { Syntax.mk_star $1 $3 }
   | formula OR formula
     {  failwith "TODO21"
       (*if Config.parse_debug() then parse_warning "deprecated use of |"  ; pconjunction (purify $1) $3*) }
   | formula OROR formula { Syntax.mk_or $1 $3 }
   | lvariable COLON identifier
     { failwith "TODO22" (*[P_PPred("type", [Arg_var($1);Arg_string($3)])]*) }
   | jargument binop_cmp jargument { SS.mk_2 $2 $1 $3 }
   | jargument EQUALS jargument { SS.mk_2 J.Cmpeq $1 $3 }
   | L_PAREN formula R_PAREN { $2 }

%% (* trailer *)
