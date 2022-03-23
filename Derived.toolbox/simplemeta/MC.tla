---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitTxns
const_164806357573332000 == 
{ << << "x", 1 >> >>,
  << << "x", 7 >> >>,
  << << "y", 7 >> >>, 
  << << "x", 0 >> >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitData
const_164806357573333000 == 
{ << 1, "z", 1 >>, << 0, "z", 2 >>, << 0, "x", 2 >> }
----

====================================================================================================
\* Modification History
\* Created Wed Mar 23 15:26:15 EDT 2022 by bosch
