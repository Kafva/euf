package lib

import (
	clang "github.com/go-clang/clang-v3.9/clang"
)

type Function struct {
	Displayname string // Includes the full prototype string
	Name string
	ReturnType clang.TypeKind
	Arguments []clang.TypeKind 
}

func makeFunction(pair CursorPair) Function {
	return Function{
		Displayname: pair.Old.DisplayName(),
		Name: pair.Old.Spelling(),
		ReturnType: pair.Old.ResultType().Kind(),
		Arguments: pair.ArgsOld,
	}
}

type CursorPair struct {
	New clang.Cursor
	Old clang.Cursor
	ArgsNew []clang.TypeKind
	ArgsOld []clang.TypeKind
}

func (p *CursorPair) Add(cursor clang.Cursor, IsNew bool) {
	switch IsNew {
	case true:
		p.New = cursor
		AddChildTypes(cursor, p.ArgsNew)
	case false:
		p.Old = cursor
		AddChildTypes(cursor, p.ArgsOld)
	}
}
