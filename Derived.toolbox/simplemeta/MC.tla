---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitTxns
const_1648163319129142000 == 
{ << << "x", 1 >> >>,
  << << "x", 7 >> >>,
  << << "y", 7 >> >>, 
  << << "x", 2 >>, << "z", 1 >> >>,
  << << "x", 1 >>, << "y", 3 >>, << "z", 0 >> >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitData
const_1648163319129143000 == 
{ << 0, "x", 1 >>, << 0, "y", 2 >>, << 0, "z", 2 >> }
----

====================================================================================================
\* Modification History
\* Created Thu Mar 24 19:08:39 EDT 2022 by bosch
