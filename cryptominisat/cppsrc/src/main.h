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

#ifndef MAIN_H
#define MAIN_H

#include <string>
#include <vector>
#include <memory>
#include <fstream>

#include "argparse.hpp"
#include "main_common.h"
#include "solverconf.h"
#include "cryptominisat.h"

using std::string;
using std::vector;

using namespace CMSat;

class Main: public MainCommon
{
    public:
        Main(int argc, char** argv);
        ~Main()
        {
            if (fratf) {
                fflush(fratf);
                fclose(fratf);
            }

            delete solver;
        }

        void parseCommandLine();
        virtual int solve();

    private:
        //arguments
        int argc;
        char** argv;
        string var_elim_strategy;
        void check_options_correctness();
        void manually_parse_some_options();
        void parse_restart_type();
        void parse_polarity_type();
        void check_num_threads_sanity(const unsigned thread_num) const;
        argparse::ArgumentParser program = argparse::ArgumentParser("cryptominisat5");

    protected:
        //Options
        virtual void add_supported_options();
        virtual void call_after_parse() {}
        SATSolver* solver = NULL;

        //File reading
        void readInAFile(SATSolver* solver2, const string& filename);
        void readInStandardInput(SATSolver* solver2);
        void parseInAllFiles(SATSolver* solver2);

        //Helper functions
        void printResultFunc(
            std::ostream* os
            , const bool toFile
            , const lbool ret
        );
        void printVersionInfo();
        int correctReturnValue(const lbool ret) const;
        lbool multi_solutions();
        void ban_found_solution();

        //Config
        std::string debugLib;
        int printResult = true;
        string commandLine;
        uint32_t max_nr_of_solutions = 1;
        bool dont_ban_solutions = false;
        int sql = 0;
        string sqlite_filename;
        uint64_t maxconfl;

        //Sampling vars
        vector<uint32_t> sampling_vars;
        std::string sampling_vars_str = "";
        bool only_sampling_solution = false;
        std::string assump_filename;
        vector<Lit> assumps;


        //Files to read & write
        bool fileNamePresent;
        string result_fname;
        string input_file;
        std::ofstream* resultfile = NULL;

        //Drat checker
        bool clause_ID_needed = false;
};

#endif //MAIN_H
