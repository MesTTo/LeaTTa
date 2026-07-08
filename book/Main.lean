-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual

import Docs

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Docs

open Verso.Output.Html in
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraFiles := [("static", "static")]
  extraHead := #[
    {{<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@500;700&display=swap"/>}},
    {{<link rel="stylesheet" href="/static/theme.css"/>}}
  ]

def main := manualMain (%doc Docs) (config := config)
