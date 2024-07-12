// CaDiCaL Solver API Extension (Christoph Jabs)
// To be included in the public interface of `Solver` in `cadical.hpp`

int64_t propagations() const;
int64_t decisions() const;
int64_t conflicts() const;
