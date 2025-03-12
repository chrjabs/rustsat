/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "gtest/gtest.h"
extern "C" {
#include "src/ipasir.h"
}

TEST(ipasir_interface, start)
{
    void* s = ipasir_init();
    ipasir_release(s);
}

TEST(ipasir_interface, sat)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    int val = ipasir_val(s, 1);
    EXPECT_EQ(val, 1);

    ipasir_release(s);
}

TEST(ipasir_interface, sat2)
{
    void* s = ipasir_init();
    ipasir_add(s, -1);
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    ipasir_add(s, 1);
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    int val = ipasir_val(s, 1);
    EXPECT_EQ(val, 1);
    val = ipasir_val(s, 2);
    EXPECT_EQ(val, 2);

    ipasir_release(s);
}

TEST(ipasir_interface, sat4)
{
    void* s = ipasir_init();
    ipasir_add(s, -2);
    ipasir_add(s, -3);
    ipasir_add(s, 0);

    ipasir_add(s, -1);
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    ipasir_add(s, 1);
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    int val = ipasir_val(s, 1);
    EXPECT_EQ(val, 1);

    val = ipasir_val(s, 2);
    EXPECT_EQ(val, 2);

    val = ipasir_val(s, 3);
    EXPECT_EQ(val, -3);

    ipasir_release(s);
}


TEST(ipasir_interface, unsat)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 0);
    ipasir_add(s, -1);
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    ipasir_release(s);
}

TEST(ipasir_interface, unsat2)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    ipasir_add(s, -1);
    ipasir_add(s, -2);
    ipasir_add(s, 0);

    ipasir_add(s, 1);
    ipasir_add(s, -2);
    ipasir_add(s, 0);

    ipasir_add(s, -1);
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    ipasir_release(s);
}

TEST(ipasir_interface, unsat_empty)
{
    void* s = ipasir_init();
    ipasir_add(s, 0);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    ipasir_release(s);
}


TEST(ipasir_interface, assump)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    int used = ipasir_failed(s, -1);
    EXPECT_EQ(used, 1);

    ipasir_release(s);
}

TEST(ipasir_interface, assump_multi)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);
    EXPECT_EQ(ipasir_failed(s, -1), 1);

    //Redo with 2
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    ipasir_assume(s, -2);
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);
    EXPECT_EQ(ipasir_failed(s, -1), 0);
    EXPECT_EQ(ipasir_failed(s, -2), 1);

    //final, it should be SAT
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    ipasir_release(s);
}

TEST(ipasir_interface, assump_multi2)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 2);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    //add assump 2 as well
    ipasir_assume(s, -1);
    ipasir_assume(s, -2);
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);
    EXPECT_EQ(ipasir_failed(s, -1), 1);
    EXPECT_EQ(ipasir_failed(s, -2), 1);

    //final, it should be SAT
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    ipasir_release(s);
}

TEST(ipasir_interface, assump_multi3)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 3);
    ipasir_add(s, 0);

    ipasir_add(s, -7);
    ipasir_add(s, -2);
    ipasir_add(s, 0);

    ipasir_add(s, 1);
    ipasir_add(s, 4);
    ipasir_add(s, 6);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    //one assum
    ipasir_assume(s, -1);
    ipasir_assume(s, -3);
    ipasir_assume(s, -4);
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);
    EXPECT_EQ(ipasir_failed(s, -1), 1);
    EXPECT_EQ(ipasir_failed(s, -2), 0);
    EXPECT_EQ(ipasir_failed(s, -3), 1);
    EXPECT_EQ(ipasir_failed(s, -4), 0);
    EXPECT_EQ(ipasir_failed(s, 4), 0);
    EXPECT_EQ(ipasir_failed(s, -6), 0);


    //one assum
    ipasir_assume(s, 7);
    ipasir_assume(s, 2);
    ipasir_assume(s, -6);
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);
    EXPECT_EQ(ipasir_failed(s, -1), 0);
    EXPECT_EQ(ipasir_failed(s, 2), 1);
    EXPECT_EQ(ipasir_failed(s, -3), 0);
    EXPECT_EQ(ipasir_failed(s, 7), 1);
    EXPECT_EQ(ipasir_failed(s, -6), 0);
    EXPECT_EQ(ipasir_failed(s, 6), 0);

    //final, it should be SAT
    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    ipasir_release(s);
}


TEST(ipasir_interface, assump_yevgeny)
{
    void* s = ipasir_init();

    ipasir_add(s, -1);
	ipasir_add(s, 0);

	int ret = ipasir_solve(s);
	EXPECT_EQ(ret, 10);

	ipasir_assume(s, 1);
	ret = ipasir_solve(s);
	EXPECT_EQ(ret, 20);

	int failed = ipasir_failed(s, 1);
    EXPECT_EQ(failed, 1);
}

TEST(ipasir_interface, assump2)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 2);
    ipasir_add(s, 3);
    ipasir_add(s, 4);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);
    ipasir_assume(s, -2);
    ipasir_assume(s, -3);
    ipasir_assume(s, -4);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    //We check the ASSUMPTION LITERAL, not the conflict clause!
    int used = ipasir_failed(s, -1);
    EXPECT_EQ(used, 1);
    int used2 = ipasir_failed(s, -2);
    EXPECT_EQ(used2, 1);
    int used3 = ipasir_failed(s, -3);
    EXPECT_EQ(used3, 1);
    int used4 = ipasir_failed(s, -4);
    EXPECT_EQ(used4, 1);

    ipasir_release(s);
}

TEST(ipasir_interface, assump3)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 2);
    ipasir_add(s, -3);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);
    ipasir_assume(s, -2);
    ipasir_assume(s, 3);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    int used = ipasir_failed(s, -1);
    EXPECT_EQ(used, 1);
    int used2 = ipasir_failed(s, -2);
    EXPECT_EQ(used2, 1);
    int used3 = ipasir_failed(s, 3);
    EXPECT_EQ(used3, 1);

    ipasir_release(s);
}

TEST(ipasir_interface, assump_clears)
{
    void* s = ipasir_init();
    ipasir_add(s, 1);
    ipasir_add(s, 0);

    ipasir_assume(s, -1);

    int ret = ipasir_solve(s);
    EXPECT_EQ(ret, 20);

    ret = ipasir_solve(s);
    EXPECT_EQ(ret, 10);

    ipasir_release(s);
}

TEST(ipasir_interface, ipasir_assump_beyond_problemvars)
{
    void* s = ipasir_init();
    ipasir_add(s, -7);
    ipasir_add(s, 0);
    ipasir_assume(s, 10);
    int ret = ipasir_solve(s);
    ASSERT_EQ(ret, 10);

    EXPECT_EQ(ipasir_val(s, 10), 10);
}

TEST(ipasir_interface, ipasir_val)
{
    void* s = ipasir_init();
    ipasir_add(s, -7);
    ipasir_add(s, 0);
    ipasir_add(s, 8);
    ipasir_add(s, 0);
    int ret = ipasir_solve(s);
    ASSERT_EQ(ret, 10);

    EXPECT_EQ(ipasir_val(s, -7), -7);
    EXPECT_EQ(ipasir_val(s, 7), -7);
    EXPECT_EQ(ipasir_val(s, -8), 8);
    EXPECT_EQ(ipasir_val(s, 8), 8);
}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
