% An implementation of the bagof predicate in Teyjus.  
% Makes use of the file system to have solutions to goals persist 
% over failures.  Compare to implementations of bagof or setof 
% that use assert within Prolog for that same purpose.
% A file called "temp" in the current directory is used for storing 
% the bag.

module bags.

% Locally defined predicates

type fileof         (A -> o) -> string -> o.
type openNclose     (in_stream -> o) -> string -> o.
type openNclose'    (in_stream -> o) -> in_stream -> o.
type file2list      string -> list A -> o.
type file2list'     list A -> in_stream -> o.

% failure-driven loop

fdloop Goal Done :- (Goal, fail) ; Done.

fileof P FileName :-
  open_out FileName Out,
  fdloop 
    (P X, term_to_string X String, output Out String, output Out ".\n")
    (close_out Out).

openNclose Goal FileName :- open_in FileName In, openNclose' Goal In.

openNclose' Goal In :- Goal In, !, close_in In.
openNclose' Goal In :- close_in In, fail.

file2list FileName L :- openNclose (file2list' L) FileName.

file2list' nil In :- eof In, !.
file2list' (X::L) In :- readterm In X, file2list' L In.

bagof P L :- fileof P "temp", file2list "temp" L, !.

%% Example: 
% [bags] ?- bagof (x\ x = 1 ; x = 2) L.
% 
% The answer substitution:
% L = 1 :: 2 :: nil
%

% The following raises a segmentation fault.
% bug :- openNclose (x\ print "Boo\n") "temp".

% The following succeeds
% bug :- open_in "temp" In, print "Boo\n", close_in In.

% bug :- open_in "temp" In, openNclose' (x\ print "Boo\n") In.

