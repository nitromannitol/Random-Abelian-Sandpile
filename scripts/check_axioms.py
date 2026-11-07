#!/usr/bin/env python3
"""Require one axiom report for each theorem of RandomSandpileAudit/Axioms.lean, listing no axiom
other than propext, Classical.choice and Quot.sound.

    lake env lean RandomSandpileAudit/Axioms.lean 2>&1 | tee axioms-audit.log
    python3 scripts/check_axioms.py axioms-audit.log

The literature inputs are hypotheses of the theorems, not axioms. Lean may wrap a long report over
several lines; each report is joined before it is read.
"""
import re
import sys

# Numbered result -> its Lean theorems in RandomSandpile/Assembly/Main.lean. A result proved from
# literature inputs is reported through its theorem; the inputs are hypotheses of that theorem.
results = {
    'Theorem 1.1': ['RandomSandpile.mainTheoremLawRadius_final', 'RandomSandpile.mainTheorem_final'],
    'Proposition 3.1': ['RandomSandpile.leastAction_final'],
    'Proposition 3.2': ['RandomSandpile.abelianDecomposition_final'],
    'Proposition 3.3': ['RandomSandpile.burning_final'],
    'Proposition 3.4': ['RandomSandpile.recurrentOfToppled_final'],
    'Lemma 5.1': ['RandomSandpile.stabilizingLegal_final'],
    'Lemma 5.2': ['RandomSandpile.abp_final'],
    'Proposition 5.1': ['RandomSandpile.concaveEnvelopeRep_final'],
    'Lemma 5.3': ['RandomSandpile.mongeAmpereRep_final'],
    'Lemma 5.4': ['RandomSandpile.muBounded_final'],
    'Proposition 5.2': ['RandomSandpile.harnackQuadratic_final'],
    'Proposition 5.3': ['RandomSandpile.subadditiveErgodic_final'],
    'Lemma 5.5': ['RandomSandpile.muConvergence_final'],
    'Lemma 6.1': ['RandomSandpile.muMonotone_final'],
    'Lemma 6.2': ['RandomSandpile.strictConcavityBeta_final', 'RandomSandpile.strictConcavity_final'],
    'Lemma 6.3': ['RandomSandpile.muLipschitz_final'],
    'Lemma 6.4': ['RandomSandpile.effectiveOperatorBasic_final'],
    'Lemma 7.1': ['RandomSandpile.oneDimToppling_final'],
    'Lemma 7.2': ['RandomSandpile.compactness_final'],
    'Lemma 7.3': ['RandomSandpile.divisibleHomogenize_final'],
    'Lemma 7.4': ['RandomSandpile.odometerLowerBound_final'],
    'Lemma 7.5': ['RandomSandpile.flat_final'],
    'Lemma 7.6': ['RandomSandpile.pegdenSmartRegularity_final'],
    'Proposition 8.1': ['RandomSandpile.divisibleLeastAction_final'],
    'Lemma 8.1': ['RandomSandpile.divisibleHomogenizeDomain_final'],
    'Theorem 8.2': ['RandomSandpile.divisibleTheorem_final'],
    'Theorem 9.1': ['RandomSandpile.openBoundaryTheorem_final'],
    'Theorem 9.2': ['RandomSandpile.singleSourceTheoremRecurrent_final',
                    'RandomSandpile.singleSourceTheoremRecurrentVT_final',
                    'RandomSandpile.recurrentOperatorIdentification_final',
                    'RandomSandpile.recurrentOperatorZeroBackgroundDifference_final'],
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}

if len(results) != 28:
    raise SystemExit(f'The list must have the 28 numbered results, not {len(results)}')
expected = [name for names in results.values() for name in names]
if len(set(expected)) != len(expected):
    raise SystemExit('A theorem is listed twice')
if len(sys.argv) != 2:
    raise SystemExit('Usage: check_axioms.py <log of RandomSandpileAudit/Axioms.lean>')
with open(sys.argv[1], encoding='utf-8') as handle:
    log = handle.read()
if re.search(r'(^|[\s:])error:|warning:|sorryAx|declaration uses .sorry', log,
             re.IGNORECASE | re.MULTILINE):
    raise SystemExit('The axiom audit emitted an error or a warning, or reported sorryAx')
reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
                     log, re.S)
seen = set()
for name, axioms, _ in reports:
    if name not in expected or name in seen:
        raise SystemExit('Unexpected or repeated axiom report: ' + name)
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    if not actual <= standard:
        raise SystemExit('Nonstandard axioms for ' + name + ': ' + ', '.join(sorted(actual - standard)))
    seen.add(name)
missing = [name for name in expected if name not in seen]
if missing:
    raise SystemExit('Missing axiom reports: ' + ', '.join(missing))
print(f'All {len(results)} numbered results checked: the {len(expected)} theorems use only propext, '
      'Classical.choice and Quot.sound.')
