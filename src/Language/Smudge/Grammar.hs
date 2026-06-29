-- Copyright 2017 Bose Corporation.
-- This software is released under the 3-Clause BSD License.
-- The license can be viewed at https://github.com/smudgelang/smudge/blob/master/LICENSE

{-# LANGUAGE DeriveFunctor #-}

module Language.Smudge.Grammar (
    Module(..),
    StateMachine(..),
    State(..),
    Event(..),
    QEvent,
    Function(..), fnName,
    SideEffect(..), seName,
    EventHandler,
    StateFlag(..),
    WholeState,
) where

data Module a = Module String [StateMachine a]

data StateMachine a = StateMachine a | StateMachineSame
    deriving (Show, Eq, Ord, Functor)

data State a = State a | StateAny | StateSame | StateEntry
    deriving (Show, Eq, Ord, Functor)

data Event a = Event a | EventAny a | EventEnter | EventExit
    deriving (Show, Eq, Ord, Functor)

type QEvent a = (StateMachine a, Event a)

data Function a = FuncVoid a | FuncEvent (QEvent a)
    deriving (Show, Eq, Ord)

fnName (FuncVoid f) = f
fnName (FuncEvent (_, Event e)) = e

data SideEffect a = SideEffect { seFn :: (Function a), seArgs :: [Function a] }
    deriving (Show, Eq, Ord)

seName = fnName . seFn

type EventHandler a = (Event a, [SideEffect a], State a)

data StateFlag = Initial
    deriving (Show, Eq, Ord)

type WholeState a = (State a, [StateFlag], [SideEffect a], [EventHandler a], [SideEffect a])
