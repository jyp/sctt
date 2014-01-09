{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Ident where

import Data.Function (on)
import Data.Char
import Numeric
import Display

instance Pretty Id where
  pretty i = text $ show i

type Name = String

newtype Unique = Unique Int deriving (Eq,Ord,Enum)

instance Show Unique where
    show (Unique (-1)) = ""
    show (Unique i) = showIntAtBase n at i ""
      where
        alpha = map intToDigit [0..9] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "'"
        n = length alpha
        at = (alpha !!)

data Id = Id
    { id_name   :: Name
    , id_unique :: Unique
    , id_m_loc  :: Maybe (Int,Int)
    -- ^ Maybe a source location this identifier appeared at
    }

instance Show Id where
    show (Id n i _) = n ++ "_" ++ show i

mkId :: Name -> Unique -> Id
mkId n u = Id n u Nothing

unsafeId :: Name -> Id
unsafeId n = Id n (Unique (error "unsafeId")) Nothing

instance Eq Id where
    (==) = (==) `on` id_unique

instance Ord Id where
    compare = compare `on` id_unique

