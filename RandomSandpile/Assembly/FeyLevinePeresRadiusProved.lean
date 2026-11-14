import RandomSandpile.Assembly.Main
import LatticeProb.External.FeyLevinePeresRadiusProved

/-!
# The recurrent single-source theorem

The radius bound of Fey, Levine and Peres discharges the corresponding hypothesis in the
single-source theorem for recurrent backgrounds.
-/

namespace RandomSandpile

/-- The recurrent single-source theorem, using the radius bound of Fey, Levine and Peres. -/
theorem singleSourceTheoremRecurrent_of_feyLevinePeresRadius
    (hAlexandrov : AlexandrovStmt) : SingleSourceTheoremRecurrentStmt :=
  singleSourceTheoremRecurrent_final LatticeProb.External.feyLevinePeresRadius_holds hAlexandrov

end RandomSandpile
