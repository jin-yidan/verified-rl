-- RLGeneralization.Draft: frontier modules excluded from the trusted root.
--
-- These files build, but contain vacuous theorems, thin wrappers,
-- or pure hypothesis-forwarding, so they are not part of the
-- trusted benchmark target.

-- Bellman rank and GOLF (has vacuous theorem)
import RLGeneralization.BilinearRank.Basic

-- Offline RL function approximation (hypothesis-forwarding wrappers)
import RLGeneralization.OfflineRL.FunctionApprox
-- POMDP belief MDP (thin wrappers over POMDP module)
import RLGeneralization.MDP.POmdpBeliefMDP
