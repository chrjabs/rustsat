from rustsat import Lit, Cnf, VarManager
from typing import List, final

@final
class Bitwise:
    def __new__(cls, lits: List[Lit]) -> "Bitwise": ...
    def n_lits(self) -> int: ...
    def n_clauses(self) -> int: ...
    def n_vars(self) -> int: ...
    def encode(self, var_manager: VarManager) -> Cnf: ...

@final
class Commander:
    def __new__(cls, lits: List[Lit]) -> "Commander": ...
    def n_lits(self) -> int: ...
    def n_clauses(self) -> int: ...
    def n_vars(self) -> int: ...
    def encode(self, var_manager: VarManager) -> Cnf: ...

@final
class Ladder:
    def __new__(cls, lits: List[Lit]) -> "Ladder": ...
    def n_lits(self) -> int: ...
    def n_clauses(self) -> int: ...
    def n_vars(self) -> int: ...
    def encode(self, var_manager: VarManager) -> Cnf: ...

@final
class Pairwise:
    def __new__(cls, lits: List[Lit]) -> "Pairwise": ...
    def n_lits(self) -> int: ...
    def n_clauses(self) -> int: ...
    def n_vars(self) -> int: ...
    def encode(self, var_manager: VarManager) -> Cnf: ...
