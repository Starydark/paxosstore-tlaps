## Workflow
- Def **Inv** = **MsgInv** /\ **AccInv**
- Proving  **MsgInv** /\ **AccInv** $\Rightarrow$ Consistency
- Proving **Spec** $\Rightarrow$ **Inv** 

## DONE
- [x] Def **Inv** = **MsgInv** /\ **AccInv**
- [x] Proving **MsgInv** /\ **AccInv** $\Rightarrow$ Consistency

## TODO 
- [x] Proving **Spec** $\Rightarrow$ **Inv** 
  - [x] Proving  **MsgInv** /\ **AccInv** $\Rightarrow$ **SafeAtStable**
    - [x] Prepare => SafeAtStable
    - [x] Accept => SafeAtStable
    - [x] OnMessage => SafeAtStable
  - [ ] Proving **Spec** $\Rightarrow$ **Inv**
    - [x] Init => Inv'
    - [x] Next => Inv'
      - [x] Next => TypeOK'
        - [x] Prepare => TypeOK'
        - [x] Accept => TypeOK'
        - [x] OnMessage => TypeOK'
      - [x] Next => AccInv'
        - [x] Prepare => AccInv'
        - [x] Accept => AccInv'
        - [x] OnMessage => AccInv'
      - [x] Next => MsgInv'
        - [x] Prepare => MsgInv'
        - [x] Accept => MsgInv'
        - [x] OnMessage => MsgInv'
