module harness.
accumulate fib.
%accumulate arith.
type announce, spy    o -> o.
type bracket          string -> o -> string -> o.  % Auxiliary

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).

type if   o -> o -> o -> o.
if P Q R :- P, !, Q.
if P Q R :- R.

% Configure the user profile name and the name of the language
config_profile  "lambdaProlog-farah".
config_language "ipfs:bafkreicwbhw5hc3ble7puleit773fmqassjrhy6xry4klsu6fh7kjarzwu".

% Specialize the file input and output functions.

openOutput File Ext Goal :- OutFile is (File ^ Ext), open_out OutFile Out,
  (pi Term\ pi String\ pprintterm Term :- term_to_string Term String, output Out String) =>
  (pi String\ pprint String :- output Out String) =>
  (closeOut :- close_out Out) => Goal.

openInput File Ext Goal :- InFile is (File ^ Ext), open_in InFile In,
  (pi String\ rread String :- input_line In String) =>
  (pi Term\ rreadterm Term :- readterm In Term) =>
  (eeof :- eof In) => (closeIn :- close_in In) => Goal.

% The top-level command.  See comments in the harness.sig file.

json File :- openOutput File ".json" (
  print_preamble File,  print_assertions File, print_named File,
  print_declarations File, closeOut), !.

print_preamble File :-
  pprint "{\n    \"format\": \"sequence\",\n    \"name\": \"",
  pprint File, pprint "\",\n".

print_assertions File :- config_profile Profile,
  pprint "    \"assertions\": [\n",
  openInput File ".goals" (print_assertions_loop Profile, closeIn, pprint "  ],\n").

print_assertions_loop _ :- eeof, !.
print_assertions_loop Profile :- rreadterm (name String _),
  pprint "       {\n         \"profile\": \"", pprint Profile,
  pprint "\",\n         \"conclusion\": \"",   pprint String,
  pprint "\",\n         \"lemmas\": []\n       }", eeof, pprint "\n", !.
print_assertions_loop Profile :- pprint ",\n", print_assertions_loop Profile.

print_named File :- config_profile Profile,
  pprint "    \"named-formulas\": {\n",
  openInput File ".goals" (print_named_loop Profile File, closeIn, pprint "\n  },\n").

print_named_loop _ _ :- eeof, !.
print_named_loop Profile File :- term_to_string File FStr,
  rreadterm (name String Content), term_to_string String Str, config_language Language,
  Content,  % <--- Theorem proving done here
  pprint "        ", pprint Str, pprint ": {\n",
  pprint "            \"language\": \"",  pprint Language, pprint "\",\n",
  pprint "            \"content\": \"",   pprintterm Content, pprint "\",\n",
  pprint "            \"declaration\": ", pprint FStr, pprint "\n        }",
  eeof, print "\n", !.
print_named_loop Profile File :- pprint ",\n", print_named_loop Profile File.

print_declarations File :- config_language Language,
  pprint "  \"declarations\": {\n     \"", pprint File,
  pprint "\": {\n    \"language\": \"", pprint Language,
  pprint "\",\n      \"content\": [\n", print_sig File, pprint ",\n", print_mod File,
  pprint "\n            ]\n        }\n    }\n}\n".

% The following two predicates will dump together the .sig file and .mod file.
% The first line in each file is ignored as are completely empty lines.
print_sig File :- openInput File ".sig" (rread _, print_lines, closeIn).
print_mod File :- openInput File ".mod" (rread _, print_lines, closeIn).

print_lines :- eeof.
print_lines :- rread Line, remove_nl Line L,
               if (L = "") print_lines (term_to_string L S, pprint "        ", pprint S), eeof, !.
print_lines :- pprint ",\n", print_lines.

% Remove the one trailing newline, if any.
remove_nl S T :- C is ((size S) - 1), "\n" is (substring S C 1), !, T is (substring S 0 C).
remove_nl S S.
