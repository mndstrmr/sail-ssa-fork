`ifndef SAIL_LIBRARY
`define SAIL_LIBRARY

// The Sail unit type.
typedef enum logic [0:0] {SAIL_UNIT=0} sail_unit;

// The Sail zero-width bitvector.
typedef enum logic [0:0] {SAIL_ZWBV=0} sail_zwbv;

`ifndef SAIL_NOSTRING

function automatic sail_unit sail_print_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_print_endline

function automatic sail_unit sail_prerr_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_prerr_endline

function automatic sail_unit sail_print(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_print

function automatic sail_unit sail_prerr(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_prerr

function automatic sail_unit sail_assert(bit b, string msg);
   if (!b) begin
      $display("%s", msg);
   end;
   return SAIL_UNIT;
endfunction // sail_assert

function automatic bit sail_eq_string(string s1, string s2);
   return s1 == s2;
endfunction

function automatic string sail_concat_str(string s1, string s2);
   return {s1, s2};
endfunction

bit [7:0] sail_memory [63:0];
`else

typedef enum logic [0:0] {SAIL_NOSTRING=0} sail_nostring;

function automatic sail_unit sail_print_endline(sail_nostring s);
   return SAIL_UNIT;
endfunction // sail_print_endline

function automatic sail_unit sail_prerr_endline(sail_nostring s);
   return SAIL_UNIT;
endfunction // sail_prerr_endline

function automatic sail_unit sail_print(sail_nostring s);
   return SAIL_UNIT;
endfunction // sail_print

function automatic sail_unit sail_prerr(sail_nostring s);
   return SAIL_UNIT;
endfunction // sail_prerr

function automatic sail_unit sail_assert(bit b, sail_nostring msg);
   return SAIL_UNIT;
endfunction // sail_assert

function automatic bit sail_eq_string(sail_nostring s1, sail_nostring s2);
   return 0;
endfunction

`endif

`endif //  `ifndef SAIL_LIBRARY
