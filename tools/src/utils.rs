/// Test a solver under two sets of assumptions and assert that the result is as
/// given. This is used in the integration tests.
#[macro_export]
macro_rules! test_assignment {
    ($solver:expr, $base_assumps:expr, $assumps:expr, $result:expr) => {{
        let mut assumps = $base_assumps.clone();
        assumps.extend($assumps);
        let res = $solver.solve_assumps(&assumps).unwrap();
        if res == rustsat::solvers::SolverResult::Sat && res != $result {
            println!("{}", $solver.full_solution().unwrap());
        }
        debug_assert_eq!(res, $result);
    }};
}

/// Test a solver under given assumptions while iterating through all possible
/// assignments of the first 1-4 variables. This is used in the integration
/// tests.
#[macro_export]
macro_rules! test_all {
    ($solver:expr,
     $assumps:expr,
     $r1:expr,
     $r0:expr ) => {{
        println!("testing with assumptions {:?}", $assumps);
        println!("testing 1");
        $crate::test_assignment!($solver, $assumps, [rustsat::lit![0]], $r1);
        println!("testing 0");
        $crate::test_assignment!($solver, $assumps, [!rustsat::lit![0]], $r0);
    }};
    ($solver:expr,
     $assumps:expr,
     $r11:expr,
     $r10:expr,
     $r01:expr,
     $r00:expr ) => {{
        println!("testing with assumptions {:?}", $assumps);
        println!("testing 11");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], rustsat::lit![1]],
            $r11
        );
        println!("testing 10");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], !rustsat::lit![1]],
            $r10
        );
        println!("testing 01");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], rustsat::lit![1]],
            $r01
        );
        println!("testing 00");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], !rustsat::lit![1]],
            $r00
        );
    }};
    ($solver:expr,
     $assumps:expr,
     $r111:expr,
     $r110:expr,
     $r101:expr,
     $r100:expr,
     $r011:expr,
     $r010:expr,
     $r001:expr,
     $r000:expr ) => {{
        println!("testing with assumptions {:?}", $assumps);
        println!("testing 111");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], rustsat::lit![1], rustsat::lit![2]],
            $r111
        );
        println!("testing 110");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], rustsat::lit![1], !rustsat::lit![2]],
            $r110
        );
        println!("testing 101");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], !rustsat::lit![1], rustsat::lit![2]],
            $r101
        );
        println!("testing 100");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [rustsat::lit![0], !rustsat::lit![1], !rustsat::lit![2]],
            $r100
        );
        println!("testing 011");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], rustsat::lit![1], rustsat::lit![2]],
            $r011
        );
        println!("testing 010");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], rustsat::lit![1], !rustsat::lit![2]],
            $r010
        );
        println!("testing 001");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], !rustsat::lit![1], rustsat::lit![2]],
            $r001
        );
        println!("testing 000");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [!rustsat::lit![0], !rustsat::lit![1], !rustsat::lit![2]],
            $r000
        );
    }};
    ($solver:expr,
     $assumps:expr,
     $r1111:expr,
     $r1110:expr,
     $r1101:expr,
     $r1100:expr,
     $r1011:expr,
     $r1010:expr,
     $r1001:expr,
     $r1000:expr,
     $r0111:expr,
     $r0110:expr,
     $r0101:expr,
     $r0100:expr,
     $r0011:expr,
     $r0010:expr,
     $r0001:expr,
     $r0000:expr ) => {{
        println!("testing with assumptions {:?}", $assumps);
        println!("testing 1111");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                rustsat::lit![1],
                rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r1111
        );
        println!("testing 1110");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                rustsat::lit![1],
                rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r1110
        );
        println!("testing 1101");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                rustsat::lit![1],
                !rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r1101
        );
        println!("testing 1100");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                rustsat::lit![1],
                !rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r1100
        );
        println!("testing 1011");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                !rustsat::lit![1],
                rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r1011
        );
        println!("testing 1010");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                !rustsat::lit![1],
                rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r1010
        );
        println!("testing 1001");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                !rustsat::lit![1],
                !rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r1001
        );
        println!("testing 1000");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                rustsat::lit![0],
                !rustsat::lit![1],
                !rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r1000
        );
        println!("testing 0111");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                rustsat::lit![1],
                rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r0111
        );
        println!("testing 0110");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                rustsat::lit![1],
                rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r0110
        );
        println!("testing 0101");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                rustsat::lit![1],
                !rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r0101
        );
        println!("testing 0100");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                rustsat::lit![1],
                !rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r0100
        );
        println!("testing 0011");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                !rustsat::lit![1],
                rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r0011
        );
        println!("testing 0010");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                !rustsat::lit![1],
                rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r0010
        );
        println!("testing 0001");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                !rustsat::lit![1],
                !rustsat::lit![2],
                rustsat::lit![3]
            ],
            $r0001
        );
        println!("testing 0000");
        $crate::test_assignment!(
            $solver,
            $assumps,
            [
                !rustsat::lit![0],
                !rustsat::lit![1],
                !rustsat::lit![2],
                !rustsat::lit![3]
            ],
            $r0000
        );
    }};
}
