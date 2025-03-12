/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file
Copyright (c) 2012  Cheng-Shen Han
Copyright (c) 2012  Jie-Hong Roland Jiang

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

#pragma once

//#define DEBUG_ROW

#include <vector>
#include <cstdint>
#include <string.h>
#include <iostream>
#include <algorithm>
#include <limits>

#include "solvertypes.h"
#include "Vec.h"

namespace CMSat {

using std::vector;

class PackedMatrix;
class EGaussian;

class PackedRow
{
public:
    PackedRow() = delete;
    PackedRow& operator=(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        //start from -1, because that's wher RHS is
        for (int i = -1; i < size; i++) {
            *(mp + i) = *(b.mp + i);
        }

        return *this;
    }

    PackedRow& operator^=(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        //start from -1, because that's wher RHS is
        for (int i = -1; i < size; i++) {
            *(mp + i) ^= *(b.mp + i);
        }

        return *this;
    }

    void and_inv(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        for (int i = 0; i < size; i++) {
            *(mp + i) &= ~(*(b.mp + i));
        }
    }

    void set_and_inv(const PackedRow& a, const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        for (int i = 0; i < size; i++) {
            *(mp + i) = *(a.mp + i) & (~(*(b.mp + i)));
        }
    }

    void set_and(const PackedRow& a, const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        for (int i = 0; i < size; i++) {
            *(mp + i) = *(a.mp + i) & *(b.mp + i);
        }
    }

    uint32_t set_and_until_popcnt_atleast2(const PackedRow& a, const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        uint32_t pop = 0;
        for (int i = 0; i < size && pop < 2; i++) {
            *(mp + i) = *(a.mp + i) & *(b.mp + i);
            pop += __builtin_popcountll((uint64_t)*(mp + i));
        }

        return pop;
    }

    void xor_in(const PackedRow& b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        rhs_internal ^= b.rhs_internal;
        for (int i = 0; i < size; i++) {
            *(mp + i) ^= *(b.mp + i);
        }
    }

    inline const int64_t& rhs() const
    {
        return rhs_internal;
    }

    inline int64_t& rhs()
    {
        return rhs_internal;
    }

    inline bool isZero() const
    {
        for (int i = 0; i < size; i++) {
            if (mp[i]) return false;
        }
        return true;
    }

    inline void setZero()
    {
        memset(mp, 0, sizeof(int64_t)*size);
    }

    inline void setOne()
    {
        memset(mp, 0xff, sizeof(int64_t)*size);
    }

    inline void clearBit(const uint32_t i)
    {
        mp[i/64] &= ~(1LL << (i%64));
    }

    inline void setBit(const uint32_t i)
    {
        //SetBit(mp+i/64, i%64);
        mp[i/64] |= (1LL << (i%64));
    }

    inline void invert_rhs(const bool b = true)
    {
        rhs_internal ^= (int)b;
    }

    void swapBoth(PackedRow b)
    {
        #ifdef DEBUG_ROW
        assert(size > 0);
        assert(b.size > 0);
        assert(b.size == size);
        #endif

        int64_t* __restrict mp1 = mp-1;
        int64_t* __restrict mp2 = b.mp-1;

        uint32_t i = size+1;
        while(i != 0) {
            std::swap(*mp1, *mp2);
            mp1++;
            mp2++;
            i--;
        }
    }

    inline bool operator[](const uint32_t i) const
    {
        #ifdef DEBUG_ROW
        assert(size*64 > i);
        #endif

        return (mp[i/64] >> (i%64)) & 1;
    }

    template<class T>
    void set(
        const T& v,
        const vector<uint32_t>& var_to_col,
        const uint32_t num_cols)
    {
        assert(size == ((int)num_cols/64) + ((bool)(num_cols % 64)));

        setZero();
        for (uint32_t i = 0; i != v.size(); i++) {
            const uint32_t toset_var = var_to_col[v[i]];
            assert(toset_var != numeric_limits<uint32_t>::max());

            setBit(toset_var);
        }

        rhs_internal = v.rhs;
    }

    // using find nonbasic and basic value
    uint32_t find_watchVar(
        vector<Lit>& tmp_clause,
        const vector<uint32_t>& col_to_var,
        vector<char> &var_has_resp_row,
        uint32_t& non_resp_var);

    // using find nonbasic value after watch list is enter
    gret propGause(
        const vector<lbool>& assigns,
        const vector<uint32_t>& col_to_var,
        vector<char> &var_has_resp_row,
        uint32_t& new_resp_var,
        PackedRow& tmp_col,
        PackedRow& tmp_col2,
        PackedRow& cols_vals,
        PackedRow& cols_unset,
        Lit& ret_lit_prop
    );

    void get_reason(
        vector<Lit>& tmp_clause,
        const vector<lbool>& assigns,
        const vector<uint32_t>& col_to_var,
        PackedRow& cols_vals,
        PackedRow& tmp_col2,
        Lit prop
    );

    uint32_t popcnt() const;
    uint32_t popcnt_at_least_2() const;

private:
    friend class PackedMatrix;
    friend class EGaussian;
    friend std::ostream& operator << (std::ostream& os, const PackedRow& m);

    PackedRow(const uint32_t _size, int64_t*  const _mp) :
        mp(_mp+1)
        , rhs_internal(*_mp)
        , size(_size)
    {}

    //int __attribute__ ((aligned (16))) *const mp;
    int64_t *__restrict const mp;
    int64_t& rhs_internal;
    const int size;
};

inline std::ostream& operator << (std::ostream& os, const PackedRow& m)
{
    for(int i = 0; i < m.size*64; i++) {
        os << (int)m[i];
    }
    os << " -- rhs: " << m.rhs();
    return os;
}

inline uint32_t PackedRow::popcnt_at_least_2() const
{
    uint32_t ret = 0;
    for (int i = 0; i < size && ret < 2; i++) {
        ret += __builtin_popcountll((uint64_t)mp[i]);
    }
    return ret;
}

inline uint32_t PackedRow::popcnt() const
{
    uint32_t ret = 0;
    for (int i = 0; i < size; i++) {
        ret += __builtin_popcountll((uint64_t)mp[i]);
    }
    return ret;
}

}
