//! # VeriPB Syntax Keywords

macro_rules! keyword {
    ($name:ident, $val:literal) => {
        pub const $name: &str = $val;
    };
    ($name:ident, s = $sval:literal, l = $lval:literal) => {
        pub const $name: &str = if cfg!(feature = "short-keywords") {
            $sval
        } else {
            $lval
        };
    };
    ($name:ident, v2 = $valv2:literal, v3 = $valv3:literal) => {
        pub const $name: &str = if cfg!(feature = "version2") {
            $valv2
        } else {
            $valv3
        };
    };
}

// General file layout
keyword!(
    HEADER,
    v2 = "pseudo-Boolean proof version 2.0",
    v3 = "pseudo-Boolean proof version 3.0"
);
keyword!(FOOTER, "end pseudo-Boolean proof");
keyword!(SUBPROOF, v2 = "begin", v3 = "subproof");
keyword!(END, "end");
keyword!(OUTPUT, "output");
keyword!(CONCLUSION, "conclusion");
keyword!(PROOF, "proof");
keyword!(QED, "qed");
keyword!(PROOFGOAL, "proofgoal");

// Syntax delimiters
// keep-sorted start
keyword!(COMMENT, v2 = "*", v3 = "%");
keyword!(FALSE, "0");
keyword!(GOAL_ID, "#");
keyword!(MAP_TO, "->");
keyword!(OFF, "off");
keyword!(ON, "on");
keyword!(RULE_TERM, v2 = "", v3 = ";");
keyword!(SEP_A, v2 = ";", v3 = ":");
keyword!(SEP_AS_TERM, v2 = ";", v3 = "");
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
keyword!(IMPLIED, "i");
keyword!(IMPLIED_ADD, "ia");
keyword!(LEVEL_SET, v2 = "#", v3 = "setlvl");
keyword!(LEVEL_WIPE, v2 = "w", v3 = "wiplvl");
keyword!(NUM_CONSTRAINTS, "f");
keyword!(OBJ_EQUAL, "eobj");
keyword!(OBJ_UPDATE, "obju");
keyword!(OBJ_UPDATE_DIFF, "diff");
keyword!(OBJ_UPDATE_NEW, "new");
keyword!(ORDER_DEFINE, "def_order");
keyword!(ORDER_LOAD, "load_order");
keyword!(PBC, v2 = "red", v3 = "pbc");
keyword!(POLISH, s = "p", l = "pol");
keyword!(REDUNDANT, "red");
keyword!(RUP, s = "u", l = "rup");
keyword!(SOLUTION, "sol");
keyword!(SOLUTION_EXCLUDE, "solx");
keyword!(SOLUTION_IMPROVE, "soli");
keyword!(STRENGTHENING_TO_CORE, "strengthening_to_core");
// keep-sorted end
#[cfg(feature = "version2")]
keyword!(EQUALS_ADD, "ea");

// Order definition
// keep-sorted start
keyword!(ORDER_DEFINITION, "def");
keyword!(ORDER_REFLEXIVITY, "right");
keyword!(ORDER_TRANSITIVITY, "transitivity");
keyword!(ORDER_VARS, "vars");
keyword!(ORDER_VARS_AUX, "aux");
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
keyword!(OUTPUT_GUARANTEE_DERIVABLE, "DERIVABLE");
keyword!(OUTPUT_GUARANTEE_EQUIOPTIMAL, "EQUIOPTIMAL");
keyword!(OUTPUT_GUARANTEE_EQUISATISFIABLE, "EQUISATISFIABLE");
keyword!(OUTPUT_GUARANTEE_NONE, "NONE");
keyword!(OUTPUT_TYPE_FILE, "FILE");
keyword!(OUTPUT_TYPE_IMPLICIT, "IMPLICIT");
// keep-sorted end

// Operations
// keep-sorted start
keyword!(ADD, "+");
keyword!(DIV, "d");
keyword!(MULT, "*");
keyword!(SATURATE, "s");
keyword!(WEAKEN, "w");
// keep-sorted end
