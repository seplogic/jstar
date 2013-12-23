(********************************************************
   This file is part of jStar
        src/parsing/jlexer.mll
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)



{ (* ddino implementation of a lexer for jimple *)
(* header *)
open Lexing
open Jparser

type error =
  | Illegal_character of char
  | Unterminated_comment

exception Error of error * Lexing.lexbuf

let nest_depth = ref 0
let nest_start_pos = ref dummy_pos
let nest x =
  nest_depth := !nest_depth + 1; nest_start_pos := (x.lex_curr_p)
let unnest x =
  nest_depth := !nest_depth - 1; (!nest_depth)!=0

let convert_base src tgt n =
  assert (2 <= src);
  assert (2 <= tgt);
  let module I = Big_int in
  let src = I.big_int_of_int src in
  let tgt = I.big_int_of_int tgt in
  let (!) = Char.code in
  let int_of_char c =
    I.big_int_of_int
    (if '0' <= c && c <= '9' then !c - !'0'
    else if 'a' <= c && c <= 'z' then !c - !'a' + 10
    else if 'A' <= c && c <= 'Z' then !c - !'A' + 10
    else invalid_arg "convert_base int_of_char") in
  let char_of_int x =
    let x = I.int_of_big_int x in
    Char.chr
    (if 0 <= x && x <= 9 then !'0' + x else
    let r = !'a'+x-10 in
    if r > !'z' then invalid_arg "convert_base char_of_int" else r) in
  let ( * ) = I.mult_big_int in
  let ( + ) = I.add_big_int in
  let rec to_big_int acc i =
    if i < String.length n
    then to_big_int (src * acc + int_of_char n.[i]) (succ i)
    else acc in
  let ( / ) = I.div_big_int in
  let ( % ) = I.mod_big_int in
  let rec from_big_int ds x =
    if I.sign_big_int x = 0
    then ds
    else from_big_int (char_of_int (x % tgt) :: ds) (x / tgt) in
  let from_big_int x =
    if I.sign_big_int x = 0 then ['0'] else from_big_int [] x in
  let ds = from_big_int (to_big_int I.zero_big_int 0) in
  let b = Buffer.create 0 in
  let pp_c = Printf.bprintf b "%c" in
  List.iter pp_c ds;
  Buffer.contents b

let error_message e lb =
  match e with
    Illegal_character c ->
      Printf.sprintf "Illegal character %c found at line %d character %d.\n"
	c
	lb.lex_curr_p.pos_lnum
	(lb.lex_curr_p.pos_cnum - lb.lex_curr_p.pos_bol)
  | Unterminated_comment -> Printf.sprintf "Unterminated comment started at line %d character %d in %s.\n"
	!nest_start_pos.pos_lnum
	(!nest_start_pos.pos_cnum  - !nest_start_pos.pos_bol)
	lb.lex_curr_p.pos_fname

(* [kwd_or_else d s] is the token corresponding to [s] if there is one,
  or the default [d] otherwise. *)
let kwd_or_else =
  let keyword_table = Hashtbl.create 53 in
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok) [
    "Abduction", ABDUCTION;
    "abstract", ABSTRACT;
    "andalso", ANDALSO;
    "annotation", ANNOTATION;
    "as", AS;
    "axioms", AXIOMS;
    "boolean", BOOLEAN;
    "breakpoint", BREAKPOINT;
    "byte", BYTE;
    "case", CASE;
    "catch", CATCH;
    "char", CHAR;
    "class", CLASS;
    "default", DEFAULT;
    "define", DEFINE;
    "double", DOUBLE;
    "Emp", EMP;
    "ensures", ENSURES;
    "enum", ENUM;
    "export", EXPORT;
    "exports", EXPORTS;
    "extends", EXTENDS;
    "final", FINAL;
    "float", FLOAT;
    "Frame", FRAME;
    "from", FROM;
    "goto", GOTO;
    "if", IF;
    "implements", IMPLEMENTS;
    "Implication", IMPLICATION;
    "import", IMPORT;
    "Inconsistency", INCONSISTENCY;
    "instanceof", INSTANCEOF;
    "int", INT;
    "interface", INTERFACE;
    "interfaceinvoke", INTERFACEINVOKE;
    "lengthof", LENGTHOF;
    "long", LONG;
    "lookupswitch", LOOKUPSWITCH;
    "native", NATIVE;
    "neg", NEG;
    "new", NEW;
    "newarray", NEWARRAY;
    "newmultiarray", NEWMULTIARRAY;
    "nop", NOP;
    "null", NULL;
    "null_type", NULL_TYPE;
    "old", OLD;
    "private", PRIVATE;
    "protected", PROTECTED;
    "public", PUBLIC;
    "requires", REQUIRES;
    "return", RETURN;
    "short", SHORT;
    "specialinvoke", SPECIALINVOKE;
    "spec", SPEC;
    "static", STATIC;
    "staticinvoke", STATICINVOKE;
    "strictfp", STRICTFP;
    "synchronized", SYNCHRONIZED;
    "tableswitch", TABLESWITCH;
    "throw", THROW;
    "throws", THROWS;
    "to", TO;
    "transient", TRANSIENT;
    "unknown", UNKNOWN;
    "virtualinvoke", VIRTUALINVOKE;
    "void", VOID;
    "volatile", VOLATILE;
    "where", WHERE;
    "with", WITH;
  ];
  fun d s ->
  try Hashtbl.find keyword_table s with Not_found -> d


(* to store the position of the beginning of a comment *)
(*let comment_start_pos = ref []*)

(* error reporting *)
open Format

let report_error = function
  | Illegal_character c ->
      Format.printf  "Illegal character (%s)@\n" (Char.escaped c)
  | Unterminated_comment ->
      Format.printf "Comment not terminated@\n"

}


(* ====================================================================== *)

(* translation from Helpers's section in jimple.scc  *)

let  all = _

let  dec_digit = ['0' - '9']
let  dec_nonzero = ['1' - '9']
let  dec_constant = dec_digit+

let  hex_digit = dec_digit | ['a' - 'f'] | ['A' - 'F']
let  hex_constant = '0' ('x' | 'X') hex_digit+

let  oct_digit = ['0' - '7']
let  oct_constant = '0' oct_digit+

let  quote = '\''

let  escapable_char = '\\' | ' ' | quote | '.' | '#' | '\"' | 'n' | 't' | 'r' | 'b' | 'f'
let  escape_code = 'u' hex_digit hex_digit hex_digit hex_digit
let  escape_char = '\\' (escapable_char | escape_code)

let  not_cr_lf = [ ^ '\010' '\013']
let  not_star = [ ^ '*']
let  not_star_slash = [^ '*' '/']

let  alpha_char = ['a' - 'z'] | ['A' - 'Z']

let  simple_id_char = alpha_char | dec_digit | '_' | '$'

let  first_id_char = alpha_char | '_' | '$'

let  quotable_char = [^ '\010' '\013' '\'']

let  string_char = escape_char | ['\000' - '\033'] | ['\035' - '\091'] | ['\093' - '\127']

let  line_comment = "//" not_cr_lf*
(*let  long_comment = "/*" not_star* '*'+ (not_star_slash not_star* '*'+)* '/'*)

let  blank = (' ' | '\009')+
let  ignored_helper = (blank | line_comment)+

let  newline = ('\013' | '\010' | "\010\013")

let full_identifier =
       ((first_id_char | escape_char) (simple_id_char | escape_char)* '.')+  '$'? (first_id_char | escape_char) (simple_id_char | escape_char)*

let identifier =
      (first_id_char | escape_char) (simple_id_char | escape_char)* | "<clinit>" | "<init>"

(*let identifier =
    (first_id_char | escape_char) (simple_id_char | escape_char)* | '<' (first_id_char | escape_char) (simple_id_char | escape_char)* '>'*)

let quoted_name = quote quotable_char+ quote

let at_identifier =
  '@' (
    ("parameter" dec_digit+ ':')
    | "this" ':'
    | "caughtexception"
    | "caller")

let integer_constant = (dec_constant | hex_constant | oct_constant) 'L'?

let float_constant = ((dec_constant '.' dec_constant) (('e'|'E') ('+'|'-')? dec_constant)? ('f'|'F')?)  | ('#' (('-'? "Infinity") | "NaN") ('f' | 'F')? )

(* Translation of section Tokens of jimple.scc *)

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | "/*Source Line Pos Tag" { SOURCE_POS_TAG }
  | "*/" { SOURCE_POS_TAG_CLOSE }
  | "/*" { nest lexbuf; comment lexbuf; token lexbuf }
  | ignored_helper  { token lexbuf }
  | "," { COMMA }
  | "{" { L_BRACE }
  | "}" { R_BRACE }
  | ";" { SEMICOLON }
  | "[" { L_BRACKET }
  | "]" { R_BRACKET }
  | "(" { L_PAREN }
  | ")" { R_PAREN }
  | ":" { COLON}
  | "." { DOT }
  | ":=" { COLON_EQUALS }
  | "=" { EQUALS }
  | "&" { AND }
  | "|" { OR }
  | "||" { OROR }
  | "|->" { MAPSTO }
  | "^" { XOR }
  | "%" { MOD }
  | "cmp" { CMP }
  | "cmpl" { CMPL }
  | "cmpg" { CMPG }
  | "==" { CMPEQ }
  | "!=" { CMPNE }
  | ">" { CMPGT }
  | ">=" { CMPGE }
  | "=>" { IMP }
  | "<=>" { BIMP }
  | "<" { CMPLT }
  | "<=" { CMPLE }
  | "<<" { SHL }
  | ">>" { SHR }
  | ">>>" { USHR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MULT }
  | "/" { DIV }
  | "?" { QUESTIONMARK }
  | "!" { BANG }
  | "|-" { VDASH }
  | eof { EOF }

  | at_identifier as s { kwd_or_else (AT_IDENTIFIER s) s }
  | full_identifier as s { kwd_or_else (FULL_IDENTIFIER s) s }
  | quoted_name as s { kwd_or_else (QUOTED_NAME s) s }
  | identifier as s { kwd_or_else (IDENTIFIER s) s }
    (* NOTE: order is important: octals, then hex, then decimals *)
    (* NOTE(rgrig): In Java, '_' should be ignored.  I *guess* soot won't ever
    generate underscores in integer literals. *)
  | '0' (oct_digit+ as n) ('l' | 'L')?
      { INTEGER_CONSTANT (convert_base 8 10 n) }
  | '0' ('x' | 'X') (hex_digit+ as n) ('l' | 'L')?
      { INTEGER_CONSTANT (convert_base 16 10 n) }
  | (dec_digit+ as n) ('l' | 'L')?
      { INTEGER_CONSTANT n }
  | float_constant as n  { FLOAT_CONSTANT n }

  (* FIXME: What is the right lexing of string constants? *)
  | '"' (string_char* as s) '"' { STRING_CONSTANT s }
  | _ as s { failwith (error_message (Illegal_character s) lexbuf) }
and comment = parse
  | "/*"  { nest lexbuf; comment lexbuf }
  | "*/"  { if unnest lexbuf then comment lexbuf }
  | newline  { Lexing.new_line lexbuf; comment lexbuf }
  | eof      { failwith (error_message Unterminated_comment lexbuf)}
  | _     { comment lexbuf; }


(* ====================================================================== *)


{ (* trailer *)
}
