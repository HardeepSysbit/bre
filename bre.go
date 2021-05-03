package bre

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"log"
	"strconv"
	"strings"
)

type BrePkg struct {
	PkgName   string    `json:"packageName"`
	ValidFrom string    `json:"validFrom"`
	ValidTo   string    `json:"validTo"`
	RuleSet   []ruleSet `json:"ruleSet"`
	Filters   []string  `json:"filters"`
}

type ruleSet struct {
	RuleName string   `json:"ruleName"`
	Rule     string   `json:"rule"`
	Actions  []string `json:"actions"`
}

type astNode struct {
	name       string
	expr       ast.Expr
	actionExpr []ast.Expr
}

var astNodes map[string]*astNode
var filters map[string]struct{}
var brePackage BrePkg

func SetBrePkg(pBrePackage []byte) (success bool, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error in Function SetBrePkg : %s", r)
		}
	}()

	// Zero Byte struct for MAP with Key and no Value
	var empty struct{}

	// Create Dimensions
	filters = make(map[string]struct{})

	// Unmarshall
	if err := json.Unmarshal(pBrePackage, &brePackage); err != nil {
		panic(err)
	}

	// Setp the dimensions
	for _, v := range brePackage.Filters {
		filters[v] = empty
	}

	// Create AST nodes
	compileErr := compile(&brePackage)
	if compileErr != nil {
		panic(compileErr)
	}

	return true, nil
}

// With the facts provide, iterate through all the rules and corresponding actions in the ruleset.
func ExeBrePkg(factBody []byte) (results map[string]string, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error in Function ExeBrePkg : %s", r)
		}
	}()

	// Setup facts collection to store existing table, modify and add new facts
	var facts map[string]string

	// Import facts received into facts collection
	if err := json.Unmarshal(factBody, &facts); err != nil {
		panic(err)
	}

	// Start trace
	facts["trace"] = ""

	// Traverse through all rules in the ruleset
	for _, v := range brePackage.RuleSet {
		exeAstNodes(v.RuleName, v.Actions, &facts, &filters)
	}

	return facts, nil
}

// Parse the BRE package into AST nodes
func compile(brePackage *BrePkg) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error in compile : %s", r)
		}
	}()

	// Create dictionary to store the AST nodes
	astNodes = make(map[string]*astNode)

	for _, rule := range brePackage.RuleSet {
		ruleExpr, ruleErr := parser.ParseExpr(rule.Rule)
		if ruleErr != nil {
			panic(ruleErr)
		}

		// spew.Dump(ruleExpr)

		astNodes[rule.RuleName] = &astNode{name: rule.RuleName, expr: ruleExpr}

		for _, action := range rule.Actions {
			actionExpr, actionErr := parser.ParseExpr(action)

			// For Debugging Purpose
			//	spew.Dump(actionExpr)

			if actionErr != nil {
				log.Fatal(actionErr)
			}

			astNodes[rule.RuleName].actionExpr = append(astNodes[rule.RuleName].actionExpr, actionExpr)
		}

	}

	return nil
}

func exeAstNodes(ruleName string, actions []string, facts *map[string]string, filters *map[string]struct{}) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error in exeAstNodes : %s", r)
		}
	}()

	astNode := astNodes[ruleName]
	rule := astNode.expr

	if eval(rule, true, true, 0, facts, filters) == "true" {

		(*facts)["trace"] = (*facts)["trace"] + ruleName + ";"

		for _, action := range astNode.actionExpr {
			eval(action, false, true, 0, facts, filters)
		}

	}

	return nil
}

func eval(exp ast.Expr, isRule bool, isLeft bool, cnt int, facts *map[string]string, filters *map[string]struct{}) string {
	switch exp := exp.(type) {
	case *ast.BinaryExpr:
		return evalBinaryExpr(exp, isRule, isLeft, cnt, facts, filters)
	case *ast.BasicLit:
		switch exp.Kind {
		case token.INT:
			return exp.Value
		case token.STRING:
			return exp.Value
		}
	case *ast.ParenExpr:
		return eval(exp.X, isRule, isLeft, cnt, facts, filters)
	case *ast.Ident:

		// Assignment
		if isRule {
			return exp.Name
		} else {
			if strings.HasPrefix(exp.Name, "_") {
				return exp.Name[1:]
			} else {
				v, exist := (*facts)[exp.Name]
				if exist {
					return fmt.Sprintf("%v", v)
				} else {
					return exp.Name
				}
			}

		}
	}
	return ""
}

func evalBinaryExpr(exp *ast.BinaryExpr, isRule bool, isLeft bool, cnt int, facts *map[string]string, filters *map[string]struct{}) string {

	left := eval(exp.X, isRule, true, cnt+1, facts, filters)
	right := eval(exp.Y, isRule, false, cnt+1, facts, filters)

	switch exp.Op {
	case token.ADD:
		leftFloat := strToFloat64(left)
		rightFloat := strToFloat64(right)

		ans := leftFloat + rightFloat

		return fmt.Sprintf("%.2f", ans)

	case token.SUB:
		leftFloat := strToFloat64(left)
		rightFloat := strToFloat64(right)

		ans := leftFloat - rightFloat

		return fmt.Sprintf("%.2f", ans)
	case token.MUL:
		leftFloat := strToFloat64(left)
		rightFloat := strToFloat64(right)

		ans := leftFloat * rightFloat

		return fmt.Sprintf("%.2f", ans)
	case token.QUO:
		leftFloat := strToFloat64(left)
		rightFloat := strToFloat64(right)

		ans := leftFloat / rightFloat

		return fmt.Sprintf("%.2f", ans)
	case token.LAND:
		if left == "true" && right == "true" {
			return "true"
		} else {
			return "false"
		}
	case token.LOR:
		if left == "true" || right == "true" {
			return "true"
		} else {
			return "false"
		}
	case token.NEQ:
		// Check Dimension
		if strings.HasPrefix(right, "xls") {
			v, exist := (*facts)[left]
			if exist {
				key := fmt.Sprintf("%s-%v", right, v)
				_, x := (*filters)[key]
				if x {
					return "true"
				} else {
					return "false"
				}

			} else {
				return "false"
			}
		} else {

			isEql := (*facts)[left] != right

			if isEql {
				return "true"
			} else {
				return "false"
			}

		}

	case token.EQL:
		// Rule or Action
		if isRule {
			// Check Dimension
			if strings.HasPrefix(right, "xls") {
				v, exist := (*facts)[left]
				if exist {
					key := fmt.Sprintf("%s-%v", right, v)
					_, x := (*filters)[key]
					if x {
						return "true"
					} else {
						return "false"
					}

				} else {
					return "false"
				}
			} else {

				isEql := (*facts)[left] == right

				if isEql {
					return "true"
				} else {
					return "false"
				}

			}

		} else {
			// Assignment
			(*facts)[string(left)] = right
		}

	}

	return ""
}

func strToFloat64(value string) float64 {
	floatNbr, err := strconv.ParseFloat(value, 64)
	if err != nil {
		log.Fatalf("Unable to convert %v to float", value)
	}

	return floatNbr
}
