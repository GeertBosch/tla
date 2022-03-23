---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitTxns
const_1648074592195108000 == 
{ << << "x", 1 >> >>,
  << << "x", 7 >> >>,
  << << "y", 7 >> >>, 
  << << "x", 0 >> >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitData
const_1648074592195109000 == 
{ << 0, "x", 1 >>, << 0, "y", 2 >>, << 0, "z", 2 >> }
----

====================================================================================================
\* Modification History
\* Created Wed Mar 23 18:29:52 EDT 2022 by bosch
