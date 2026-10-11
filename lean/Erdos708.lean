-- Build root: the verified closure (FinalCheck imports every headline chain and freezes its
-- axioms with #guard_msgs) and the Section 18 statement file. Planning files with `sorry`
-- (SparseCore.lean, H97/Cards.lean, H17/Chain19/Cards.lean) are not imported.
import Erdos708.FinalCheck
import Erdos708.H883.Statement
import Erdos708.H883.Knapsack
