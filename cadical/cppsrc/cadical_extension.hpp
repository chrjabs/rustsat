// CaDiCaL Solver API Extension (Christoph Jabs)
// To be included in the public interface of `Solver` in `cadical.hpp`

int64_t propagations() const;
int64_t decisions() const;
int64_t conflicts() const;

bool prop_check(const int *assumps, size_t assumps_len, bool psaving,
                void (*prop_cb)(void *, int), void *cb_data);
