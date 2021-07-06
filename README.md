# Dependnece analysis for a toy programming language

- [The file `depenence-loop/proof.v` proves the fundamental theorem of dependence analysis](https://github.com/bollu/dependence-analysis-coq/blob/master/dependence-loop/proof.v#L2877)

```coq
(** Main theorem of the day. If a *schedule s* respects a *complete dependence set ds*,
then the semantics of the original program is the same as that of the rescheduled program *)
 Theorem reschedulePreservesSemantics: 
   forall (c c': com) (ds: dependenceset) (s sinv: nat -> nat),
    completeDependenceSet c ds -> scheduleMappingWitness s sinv c c' ->
    scheduleRespectsDependenceSet s ds -> c === c'.
```

This implements dependence analysis for a toy programming language.

This was an exercise in learning coq for my fourth semester independent
study project.

[The report is available here](https://github.com/bollu/dependence-analysis-coq/blob/master/report-independent-study/independent-study.pdf)

Keywords for SEO in the future when I want to find this again: proof polyhedral Coq Polly dependence analysis theorem 
