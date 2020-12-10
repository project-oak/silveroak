(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Init.Byte.

Section Sbox.
  Definition forward_sbox (b : byte) :=
    match b with
    | x00 => x63
    | x01 => x7c
    | x02 => x77
    | x03 => x7b
    | x04 => xf2
    | x05 => x6b
    | x06 => x6f
    | x07 => xc5
    | x08 => x30
    | x09 => x01
    | x0a => x67
    | x0b => x2b
    | x0c => xfe
    | x0d => xd7
    | x0e => xab
    | x0f => x76
    | x10 => xca
    | x11 => x82
    | x12 => xc9
    | x13 => x7d
    | x14 => xfa
    | x15 => x59
    | x16 => x47
    | x17 => xf0
    | x18 => xad
    | x19 => xd4
    | x1a => xa2
    | x1b => xaf
    | x1c => x9c
    | x1d => xa4
    | x1e => x72
    | x1f => xc0
    | x20 => xb7
    | x21 => xfd
    | x22 => x93
    | x23 => x26
    | x24 => x36
    | x25 => x3f
    | x26 => xf7
    | x27 => xcc
    | x28 => x34
    | x29 => xa5
    | x2a => xe5
    | x2b => xf1
    | x2c => x71
    | x2d => xd8
    | x2e => x31
    | x2f => x15
    | x30 => x04
    | x31 => xc7
    | x32 => x23
    | x33 => xc3
    | x34 => x18
    | x35 => x96
    | x36 => x05
    | x37 => x9a
    | x38 => x07
    | x39 => x12
    | x3a => x80
    | x3b => xe2
    | x3c => xeb
    | x3d => x27
    | x3e => xb2
    | x3f => x75
    | x40 => x09
    | x41 => x83
    | x42 => x2c
    | x43 => x1a
    | x44 => x1b
    | x45 => x6e
    | x46 => x5a
    | x47 => xa0
    | x48 => x52
    | x49 => x3b
    | x4a => xd6
    | x4b => xb3
    | x4c => x29
    | x4d => xe3
    | x4e => x2f
    | x4f => x84
    | x50 => x53
    | x51 => xd1
    | x52 => x00
    | x53 => xed
    | x54 => x20
    | x55 => xfc
    | x56 => xb1
    | x57 => x5b
    | x58 => x6a
    | x59 => xcb
    | x5a => xbe
    | x5b => x39
    | x5c => x4a
    | x5d => x4c
    | x5e => x58
    | x5f => xcf
    | x60 => xd0
    | x61 => xef
    | x62 => xaa
    | x63 => xfb
    | x64 => x43
    | x65 => x4d
    | x66 => x33
    | x67 => x85
    | x68 => x45
    | x69 => xf9
    | x6a => x02
    | x6b => x7f
    | x6c => x50
    | x6d => x3c
    | x6e => x9f
    | x6f => xa8
    | x70 => x51
    | x71 => xa3
    | x72 => x40
    | x73 => x8f
    | x74 => x92
    | x75 => x9d
    | x76 => x38
    | x77 => xf5
    | x78 => xbc
    | x79 => xb6
    | x7a => xda
    | x7b => x21
    | x7c => x10
    | x7d => xff
    | x7e => xf3
    | x7f => xd2
    | x80 => xcd
    | x81 => x0c
    | x82 => x13
    | x83 => xec
    | x84 => x5f
    | x85 => x97
    | x86 => x44
    | x87 => x17
    | x88 => xc4
    | x89 => xa7
    | x8a => x7e
    | x8b => x3d
    | x8c => x64
    | x8d => x5d
    | x8e => x19
    | x8f => x73
    | x90 => x60
    | x91 => x81
    | x92 => x4f
    | x93 => xdc
    | x94 => x22
    | x95 => x2a
    | x96 => x90
    | x97 => x88
    | x98 => x46
    | x99 => xee
    | x9a => xb8
    | x9b => x14
    | x9c => xde
    | x9d => x5e
    | x9e => x0b
    | x9f => xdb
    | xa0 => xe0
    | xa1 => x32
    | xa2 => x3a
    | xa3 => x0a
    | xa4 => x49
    | xa5 => x06
    | xa6 => x24
    | xa7 => x5c
    | xa8 => xc2
    | xa9 => xd3
    | xaa => xac
    | xab => x62
    | xac => x91
    | xad => x95
    | xae => xe4
    | xaf => x79
    | xb0 => xe7
    | xb1 => xc8
    | xb2 => x37
    | xb3 => x6d
    | xb4 => x8d
    | xb5 => xd5
    | xb6 => x4e
    | xb7 => xa9
    | xb8 => x6c
    | xb9 => x56
    | xba => xf4
    | xbb => xea
    | xbc => x65
    | xbd => x7a
    | xbe => xae
    | xbf => x08
    | xc0 => xba
    | xc1 => x78
    | xc2 => x25
    | xc3 => x2e
    | xc4 => x1c
    | xc5 => xa6
    | xc6 => xb4
    | xc7 => xc6
    | xc8 => xe8
    | xc9 => xdd
    | xca => x74
    | xcb => x1f
    | xcc => x4b
    | xcd => xbd
    | xce => x8b
    | xcf => x8a
    | xd0 => x70
    | xd1 => x3e
    | xd2 => xb5
    | xd3 => x66
    | xd4 => x48
    | xd5 => x03
    | xd6 => xf6
    | xd7 => x0e
    | xd8 => x61
    | xd9 => x35
    | xda => x57
    | xdb => xb9
    | xdc => x86
    | xdd => xc1
    | xde => x1d
    | xdf => x9e
    | xe0 => xe1
    | xe1 => xf8
    | xe2 => x98
    | xe3 => x11
    | xe4 => x69
    | xe5 => xd9
    | xe6 => x8e
    | xe7 => x94
    | xe8 => x9b
    | xe9 => x1e
    | xea => x87
    | xeb => xe9
    | xec => xce
    | xed => x55
    | xee => x28
    | xef => xdf
    | xf0 => x8c
    | xf1 => xa1
    | xf2 => x89
    | xf3 => x0d
    | xf4 => xbf
    | xf5 => xe6
    | xf6 => x42
    | xf7 => x68
    | xf8 => x41
    | xf9 => x99
    | xfa => x2d
    | xfb => x0f
    | xfc => xb0
    | xfd => x54
    | xfe => xbb
    | xff => x16
    end.

  Definition inverse_sbox (b : byte) :=
    match b with
    | x00 => x52
    | x01 => x09
    | x02 => x6a
    | x03 => xd5
    | x04 => x30
    | x05 => x36
    | x06 => xa5
    | x07 => x38
    | x08 => xbf
    | x09 => x40
    | x0a => xa3
    | x0b => x9e
    | x0c => x81
    | x0d => xf3
    | x0e => xd7
    | x0f => xfb
    | x10 => x7c
    | x11 => xe3
    | x12 => x39
    | x13 => x82
    | x14 => x9b
    | x15 => x2f
    | x16 => xff
    | x17 => x87
    | x18 => x34
    | x19 => x8e
    | x1a => x43
    | x1b => x44
    | x1c => xc4
    | x1d => xde
    | x1e => xe9
    | x1f => xcb
    | x20 => x54
    | x21 => x7b
    | x22 => x94
    | x23 => x32
    | x24 => xa6
    | x25 => xc2
    | x26 => x23
    | x27 => x3d
    | x28 => xee
    | x29 => x4c
    | x2a => x95
    | x2b => x0b
    | x2c => x42
    | x2d => xfa
    | x2e => xc3
    | x2f => x4e
    | x30 => x08
    | x31 => x2e
    | x32 => xa1
    | x33 => x66
    | x34 => x28
    | x35 => xd9
    | x36 => x24
    | x37 => xb2
    | x38 => x76
    | x39 => x5b
    | x3a => xa2
    | x3b => x49
    | x3c => x6d
    | x3d => x8b
    | x3e => xd1
    | x3f => x25
    | x40 => x72
    | x41 => xf8
    | x42 => xf6
    | x43 => x64
    | x44 => x86
    | x45 => x68
    | x46 => x98
    | x47 => x16
    | x48 => xd4
    | x49 => xa4
    | x4a => x5c
    | x4b => xcc
    | x4c => x5d
    | x4d => x65
    | x4e => xb6
    | x4f => x92
    | x50 => x6c
    | x51 => x70
    | x52 => x48
    | x53 => x50
    | x54 => xfd
    | x55 => xed
    | x56 => xb9
    | x57 => xda
    | x58 => x5e
    | x59 => x15
    | x5a => x46
    | x5b => x57
    | x5c => xa7
    | x5d => x8d
    | x5e => x9d
    | x5f => x84
    | x60 => x90
    | x61 => xd8
    | x62 => xab
    | x63 => x00
    | x64 => x8c
    | x65 => xbc
    | x66 => xd3
    | x67 => x0a
    | x68 => xf7
    | x69 => xe4
    | x6a => x58
    | x6b => x05
    | x6c => xb8
    | x6d => xb3
    | x6e => x45
    | x6f => x06
    | x70 => xd0
    | x71 => x2c
    | x72 => x1e
    | x73 => x8f
    | x74 => xca
    | x75 => x3f
    | x76 => x0f
    | x77 => x02
    | x78 => xc1
    | x79 => xaf
    | x7a => xbd
    | x7b => x03
    | x7c => x01
    | x7d => x13
    | x7e => x8a
    | x7f => x6b
    | x80 => x3a
    | x81 => x91
    | x82 => x11
    | x83 => x41
    | x84 => x4f
    | x85 => x67
    | x86 => xdc
    | x87 => xea
    | x88 => x97
    | x89 => xf2
    | x8a => xcf
    | x8b => xce
    | x8c => xf0
    | x8d => xb4
    | x8e => xe6
    | x8f => x73
    | x90 => x96
    | x91 => xac
    | x92 => x74
    | x93 => x22
    | x94 => xe7
    | x95 => xad
    | x96 => x35
    | x97 => x85
    | x98 => xe2
    | x99 => xf9
    | x9a => x37
    | x9b => xe8
    | x9c => x1c
    | x9d => x75
    | x9e => xdf
    | x9f => x6e
    | xa0 => x47
    | xa1 => xf1
    | xa2 => x1a
    | xa3 => x71
    | xa4 => x1d
    | xa5 => x29
    | xa6 => xc5
    | xa7 => x89
    | xa8 => x6f
    | xa9 => xb7
    | xaa => x62
    | xab => x0e
    | xac => xaa
    | xad => x18
    | xae => xbe
    | xaf => x1b
    | xb0 => xfc
    | xb1 => x56
    | xb2 => x3e
    | xb3 => x4b
    | xb4 => xc6
    | xb5 => xd2
    | xb6 => x79
    | xb7 => x20
    | xb8 => x9a
    | xb9 => xdb
    | xba => xc0
    | xbb => xfe
    | xbc => x78
    | xbd => xcd
    | xbe => x5a
    | xbf => xf4
    | xc0 => x1f
    | xc1 => xdd
    | xc2 => xa8
    | xc3 => x33
    | xc4 => x88
    | xc5 => x07
    | xc6 => xc7
    | xc7 => x31
    | xc8 => xb1
    | xc9 => x12
    | xca => x10
    | xcb => x59
    | xcc => x27
    | xcd => x80
    | xce => xec
    | xcf => x5f
    | xd0 => x60
    | xd1 => x51
    | xd2 => x7f
    | xd3 => xa9
    | xd4 => x19
    | xd5 => xb5
    | xd6 => x4a
    | xd7 => x0d
    | xd8 => x2d
    | xd9 => xe5
    | xda => x7a
    | xdb => x9f
    | xdc => x93
    | xdd => xc9
    | xde => x9c
    | xdf => xef
    | xe0 => xa0
    | xe1 => xe0
    | xe2 => x3b
    | xe3 => x4d
    | xe4 => xae
    | xe5 => x2a
    | xe6 => xf5
    | xe7 => xb0
    | xe8 => xc8
    | xe9 => xeb
    | xea => xbb
    | xeb => x3c
    | xec => x83
    | xed => x53
    | xee => x99
    | xef => x61
    | xf0 => x17
    | xf1 => x2b
    | xf2 => x04
    | xf3 => x7e
    | xf4 => xba
    | xf5 => x77
    | xf6 => xd6
    | xf7 => x26
    | xf8 => xe1
    | xf9 => x69
    | xfa => x14
    | xfb => x63
    | xfc => x55
    | xfd => x21
    | xfe => x0c
    | xff => x7d
    end.
End Sbox.
