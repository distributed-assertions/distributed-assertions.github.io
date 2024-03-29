type announce, spy    o -> o.
type bracket          string -> o -> string -> o.  % Auxiliary

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).

%openOutput File Ext Goal :- announce (openOutput File Ext Goal).
%print_preamble File      :- announce (print_preamble File).
%print_assertions File    :- announce (print_assertions File).
%pprint File              :- announce (pprint File).

