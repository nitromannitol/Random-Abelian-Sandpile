import RandomSandpile.Assembly.Main
import LatticeProb.External.FeyLevinePeresRadiusProved

/-!
# The recurrent single-source theorem

The radius bound of Fey, Levine and Peres discharges the corresponding hypothesis in the
single-source theorem for recurrent backgrounds. The theorem `singleSourceTheoremRecurrent_final`
of `RandomSandpile/Assembly/Main.lean` uses the same bound and Alexandrov's theorem, both proved,
and takes no hypothesis.
-/

namespace RandomSandpile

/-- The recurrent single-source theorem, using the radius bound of Fey, Levine and Peres. -/
theorem singleSourceTheoremRecurrent_of_feyLevinePeresRadius
    (hAlexandrov : AlexandrovStmt) : SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent LatticeProb.External.feyLevinePeresRadius_holds hAlexandrov

end RandomSandpile
