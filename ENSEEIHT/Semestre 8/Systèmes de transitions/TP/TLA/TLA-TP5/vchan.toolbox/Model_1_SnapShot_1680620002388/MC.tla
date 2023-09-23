---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_168062000034088000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_168062000034089000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_168062000034090000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_168062000034091000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_168062000034092000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_168062000034095000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 16:53:20 CEST 2023 by ahamoir
