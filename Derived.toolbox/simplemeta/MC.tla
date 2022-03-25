---- MODULE MC ----
EXTENDS Derived, TLC

\* CONSTANT definitions @modelParameterConstants:1InitTxns
const_1648238378043196000 == 
{ << << "x", 1 >> >>,
  << << "x", 7 >> >>,
  << << "y", 7 >> >>, 
  << << "x", 2 >>, << "z", 1 >> >>,
  << << "x", 1 >>, << "y", 3 >>, << "z", 0 >> >> }
----

\* CONSTANT definitions @modelParameterConstants:2InitData
const_1648238378043197000 == 
{ << 0, "x", 1 >>, << 0, "y", 2 >>, << 0, "z", 2 >> }
----

\* CONSTANT definitions @modelParameterConstants:3WriteProc
const_1648238378043198000 == 
{ 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:4ReadProc
const_1648238378043199000 == 
{ 1 }
----

====================================================================================================
\* Modification History
\* Created Fri Mar 25 15:59:38 EDT 2022 by bosch
