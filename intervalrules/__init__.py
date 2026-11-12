"""Pointwise interval Datalog engine (standard library only)."""

from .engine import Engine, Rule
from . import segments

__all__ = ["Engine", "Rule", "segments"]
