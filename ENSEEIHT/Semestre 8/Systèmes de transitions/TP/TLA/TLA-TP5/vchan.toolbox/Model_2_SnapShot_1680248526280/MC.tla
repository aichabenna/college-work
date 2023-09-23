---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_168024851920184000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_168024851920185000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_168024851920186000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_168024851920187000 == 
1..8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_168024851920188000 ==
Len(Sent) < 6
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_168024851920191000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Fri Mar 31 09:41:59 CEST 2023 by ahamoir
