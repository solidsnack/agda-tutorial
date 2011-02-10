
module LogL where

open import Data.List
open import Data.String
open import Data.Nat
open import Data.Unit


data UUID : Set where
  uuid : UUID

data Log : Set where
  log : UUID → Log

data Map : Set → Set → Set where
  m : Map ⊤ ⊤    -- Haha.

data Time : Set where
  time : String → Time

data MessageID : Set where
  messageID : UUID → MessageID

data Message : Set where
  message : String → Message


data Time/L : Set where
  at : Time → Time/L

data Rewrite/L : Set where
  set   : MessageID → Message → Rewrite/L
  unset : MessageID → Rewrite/L

data Append/L : Set → Set where
  append   : Log → Message → Append/L MessageID
  search   : Log → Time/L → Append/L (List MessageID)
  retrieve : Log → List MessageID → Append/L (Map MessageID Message)
  new      : Append/L Log
  copy     : Log → Append/L Log
  update   : Log → Rewrite/L → Append/L Log

data Delete/L : Set → Set where
  delete : Log → Delete/L ⊤
