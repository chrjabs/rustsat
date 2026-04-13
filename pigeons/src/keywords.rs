//! # VeriPB Syntax Keywords

macro_rules! keyword {
    ($name:ident, $val:literal) => {
        pub const $name: &str = $val;
    };
}

// General file layout
keyword!(HEADER, "pseudo-Boolean proof version 3.0");
keyword!(FOOTER, "end pseudo-Boolean proof");
keyword!(SUBPROOF, "subproof");
keyword!(END, "end");
keyword!(OUTPUT, "output");
keyword!(CONCLUSION, "conclusion");
keyword!(PROOF, "proof");
keyword!(QED, "qed");
keyword!(PROOFGOAL, "proofgoal");
keyword!(SCOPE, "scope");
keyword!(LEQ_SCOPE, "leq");
keyword!(GEQ_SCOPE, "geq");

// Syntax delimiters
// keep-sorted start
keyword!(COMMENT, "%");
keyword!(FALSE, "0");
keyword!(GOAL_ID, "#");
keyword!(MAP_TO, "->");
keyword!(OFF, "off");
keyword!(ON, "on");
keyword!(RULE_TERM, ";");
keyword!(SEP_A, ":");
keyword!(SEP_B, ":");
keyword!(TRUE, "1");
// keep-sorted end

// Rules
// keep-sorted start
keyword!(CORE_ID, "core id");
keyword!(CORE_RANGE, "core range");
keyword!(DEL_CORE, "delc");
keyword!(DEL_DERIVED, "deld");
keyword!(DEL_ID, "del id");
keyword!(DEL_RANGE, "del range");
keyword!(DEL_SPEC, "del spec");
keyword!(DOMINATED, "dom");
keyword!(EQUALS, "e");
keyword!(FAIL, "fail");
keyword!(IMPLIED, "i");
keyword!(IMPLIED_ADD, "ia");
keyword!(IS_DELETED, "is_deleted");
keyword!(LEVEL_SET, "setlvl");
keyword!(LEVEL_WIPE, "wiplvl");
keyword!(NUM_CONSTRAINTS, "f");
keyword!(OBJ_EQUAL, "eobj");
keyword!(OBJ_UPDATE, "obju");
keyword!(OBJ_UPDATE_DIFF, "diff");
keyword!(OBJ_UPDATE_NEW, "new");
keyword!(ORDER_DEFINE, "def_order");
keyword!(ORDER_LOAD, "load_order");
keyword!(PBC, "pbc");
keyword!(POLISH, "pol");
keyword!(REDUNDANT, "red");
keyword!(RUP, "rup");
keyword!(SOLUTION, "sol");
keyword!(SOLUTION_EXCLUDE, "solx");
keyword!(SOLUTION_IMPROVE, "soli");
keyword!(STRENGTHENING_TO_CORE, "strengthening_to_core");
keyword!(TIMER_END, "end_time");
keyword!(TIMER_START, "start_time");
// keep-sorted end

// Order definition
// keep-sorted start
keyword!(ORDER_DEFINITION, "def");
keyword!(ORDER_REFLEXIVITY, "reflexivity");
keyword!(ORDER_SPECIFICATION, "spec");
keyword!(ORDER_TRANSITIVITY, "transitivity");
keyword!(ORDER_VARS, "vars");
keyword!(ORDER_VARS_AUX, "aux");
keyword!(ORDER_VARS_FRESH_AUX_1, "fresh_aux_1");
keyword!(ORDER_VARS_FRESH_AUX_2, "fresh_aux_2");
keyword!(ORDER_VARS_FRESH_RIGHT, "fresh_right");
keyword!(ORDER_VARS_LEFT, "left");
keyword!(ORDER_VARS_RIGHT, "right");
// keep-sorted end

// Output & conclusion
// keep-sorted start
keyword!(CONCLUSION_BOUNDS, "BOUNDS");
keyword!(CONCLUSION_NONE, "NONE");
keyword!(CONCLUSION_SAT, "SAT");
keyword!(CONCLUSION_UNSAT, "UNSAT");
keyword!(OPB, "opb");
keyword!(OUTPUT_GUARANTEE_DERIVABLE, "DERIVABLE");
keyword!(OUTPUT_GUARANTEE_EQUIOPTIMAL, "EQUIOPTIMAL");
keyword!(OUTPUT_GUARANTEE_EQUISATISFIABLE, "EQUISATISFIABLE");
keyword!(OUTPUT_GUARANTEE_NONE, "NONE");
keyword!(OUTPUT_TYPE_CONSTRAINTS, "CONSTRAINTS");
keyword!(OUTPUT_TYPE_FILE, "FILE");
keyword!(OUTPUT_TYPE_IMPLICIT, "IMPLICIT");
keyword!(OUTPUT_TYPE_PERMUTATION, "PERMUTATION");
// keep-sorted end

// Operations
// keep-sorted start
keyword!(ADD, "+");
keyword!(MULT, "*");
keyword!(NORM_DIV, "d");
keyword!(NORM_MIR, "n");
keyword!(SATURATE, "s");
keyword!(SUB, "-");
keyword!(VAR_DIV, "c");
keyword!(VAR_MIR, "m");
keyword!(WEAKEN, "w");
// keep-sorted end
