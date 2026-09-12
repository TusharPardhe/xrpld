namespace XRPL.Model.Protocol

inductive TER where
  | tesSUCCESS
  | tecINTERNAL
  | tecAMM_INVALID_TOKENS
  | tecAMM_FAILED
  | tecUNFUNDED_AMM
  | tecNO_ENTRY
  | tecWRONG_ASSET
  | tecOBJECT_NOT_FOUND
  | tecNO_AUTH
  | tecINSUFFICIENT_RESERVE
  | tecDIR_FULL
  | tecNO_TARGET
  | tecEXPIRED
  | tecNO_PERMISSION
  | tecDUPLICATE
  | tecNO_LINE_INSUF_RESERVE
  | tecHAS_OBLIGATIONS
  | tecNO_DST
  | tecDST_TAG_NEEDED
  | tecNO_LINE
  | tecFAILED_PROCESSING
  | tecPATH_DRY
  | tecINSUFFICIENT_FUNDS
  | tecKILLED
  | tefINTERNAL
  | tefBAD_LEDGER
  | terNO_ACCOUNT
  | terNO_RIPPLE
  | tecFROZEN
  | tecLOCKED
  | temMALFORMED
  | temBAD_AMOUNT
  | telFAILED_PROCESSING
  | temINVALID
  | temINVALID_FLAG
  | temBAD_FEE
  | temBAD_SRC_ACCOUNT
  | temDISABLED
  | tecLIMIT_EXCEEDED
  | tecPRECISION_LOSS
  | tecTOO_SOON
  | tecINSUFFICIENT_PAYMENT
  deriving DecidableEq, Repr, BEq

def TER.operator_bool : TER → Bool
  | .tesSUCCESS => false
  | _ => true

def TER.isTesSuccess : TER → Bool
  | .tesSUCCESS => true
  | _ => false

-- A `tec` result claims a fee (the tx is recorded, its effects discarded).
def TER.isTec : TER → Bool
  | .tecINTERNAL | .tecAMM_INVALID_TOKENS | .tecAMM_FAILED | .tecUNFUNDED_AMM
  | .tecNO_ENTRY | .tecWRONG_ASSET | .tecOBJECT_NOT_FOUND | .tecNO_AUTH
  | .tecINSUFFICIENT_RESERVE | .tecDIR_FULL | .tecNO_TARGET | .tecEXPIRED
  | .tecNO_PERMISSION | .tecDUPLICATE | .tecNO_LINE_INSUF_RESERVE
  | .tecHAS_OBLIGATIONS | .tecNO_DST | .tecDST_TAG_NEEDED | .tecNO_LINE
  | .tecFAILED_PROCESSING | .tecPATH_DRY | .tecINSUFFICIENT_FUNDS
  | .tecFROZEN | .tecLOCKED | .tecLIMIT_EXCEEDED | .tecPRECISION_LOSS | .tecKILLED
  | .tecTOO_SOON | .tecINSUFFICIENT_PAYMENT => true
  | _ => false

def TER.code : TER → Int32
  | .tesSUCCESS => 0
  | .tecINTERNAL => 144
  | .tecAMM_INVALID_TOKENS => 165
  | .tecAMM_FAILED => 164
  | .tecUNFUNDED_AMM => 162
  | .tecNO_ENTRY => 140
  | .tecWRONG_ASSET => 194
  | .tecOBJECT_NOT_FOUND => 160
  | .tecNO_AUTH => 134
  | .tecINSUFFICIENT_RESERVE => 141
  | .tecDIR_FULL => 121
  | .tecNO_TARGET => 138
  | .tecEXPIRED => 148
  | .tecNO_PERMISSION => 139
  | .tecDUPLICATE => 149
  | .tecNO_LINE_INSUF_RESERVE => 126
  | .tecHAS_OBLIGATIONS => 151
  | .tecNO_DST => 124
  | .tecDST_TAG_NEEDED => 143
  | .tecNO_LINE => 135
  | .tecFAILED_PROCESSING => 105
  | .tecPATH_DRY => 128
  | .tecINSUFFICIENT_FUNDS => 159
  | .tecKILLED => 150
  | .tefINTERNAL => -192
  | .tefBAD_LEDGER => -195
  | .terNO_ACCOUNT => -96
  | .terNO_RIPPLE => -90
  | .tecFROZEN => 137
  | .tecLOCKED => 192
  | .temMALFORMED => -299
  | .temBAD_AMOUNT => -298
  | .telFAILED_PROCESSING => -395
  | .temINVALID => -277
  | .temINVALID_FLAG => -276
  | .temBAD_FEE => -295
  | .temBAD_SRC_ACCOUNT => -281
  | .temDISABLED => -273
  | .tecLIMIT_EXCEEDED => 195
  | .tecPRECISION_LOSS => 197
  | .tecTOO_SOON => 152
  | .tecINSUFFICIENT_PAYMENT => 161


end XRPL.Model.Protocol
