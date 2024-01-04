package main

import (
	"fmt"
	"reflect"
	"strings"

)

// Define the data structures for Formula and Sequent
type Formula struct {
	Content string
}

type Sequent struct {
	Left  []Formula
	Right []Formula
}

// Reverse Weakening Left Rule
func ReverseWeakeningL(sequent Sequent) Sequent {
	if len(sequent.Left) == 0 {
		return sequent
	}
	newLeft := sequent.Left[1:]

	newSequent := Sequent{
		Left:  newLeft,
		Right: sequent.Right,
	}
	return newSequent
}

// Reverse Weakening Right Rule
func ReverseWeakeningR(sequent Sequent) Sequent {
	if len(sequent.Right) == 0 {
		return sequent
	}
	newRight := sequent.Right[:len(sequent.Right)-1]

	newSequent := Sequent{
		Left:  sequent.Left,
		Right: newRight,
	}
	return newSequent
}

// Reverse Contraction Right Rule Limit 1
func ReverseContractionR(sequent Sequent) Sequent {
	if len(sequent.Right) == 0 {
		return sequent
	}
	formulaIndex := len(sequent.Right) - 1
	formulaToDuplicate := sequent.Right[formulaIndex]
	newRight := append(sequent.Right, formulaToDuplicate)

	newSequent := Sequent{
		Left:  sequent.Left,
		Right: newRight,
	}
	return newSequent
}

// Reverse Contraction Left Rule Limit 1
func ReverseContractionL(sequent Sequent) Sequent {
	if len(sequent.Left) == 0 {
		return sequent
	}
	formulaIndex := 0
	formulaToDuplicate := sequent.Left[formulaIndex]
	newLeft := append(sequent.Left, formulaToDuplicate)

	newSequent := Sequent{
		Left:  newLeft,
		Right: sequent.Right,
	}
	return newSequent
}

// Reverse Exchange Left Rule Limit 2
func ReverseExchangeL(sequent Sequent, index1 int, index2 int) Sequent {
	if index1 < len(sequent.Left) && index2 < len(sequent.Left) {
		sequent.Left[index1], sequent.Left[index2] = sequent.Left[index2], sequent.Left[index1]
	}
	return sequent
}

// Reverse Exchange Right Rule Limit2
func ReverseExchangeR(sequent Sequent, index1 int, index2 int) Sequent {
	if index1 < len(sequent.Right) && index2 < len(sequent.Right) {
		sequent.Right[index1], sequent.Right[index2] = sequent.Right[index2], sequent.Right[index1]
	}
	return sequent
}

// Negation Left (¬L) Rule limit only having negation
func NegationL(sequent Sequent) Sequent {
	formulaIndex := 0
	if formulaIndex < len(sequent.Left) {
		formula := sequent.Left[formulaIndex]
		if strings.HasPrefix(formula.Content, "¬") {
			// Move negated formula to right and remove negation
			newRight := append(sequent.Right, Formula{Content: strings.TrimPrefix(formula.Content, "¬")})

			// Remove the original formula from left
			newLeft := append(sequent.Left[:formulaIndex], sequent.Left[formulaIndex+1:]...)

			newSequent := Sequent{
				Left:  newLeft,
				Right: newRight,
			}
			return newSequent
		}
	}
	return sequent
}

// Negation Right (¬R) Rule limit only having negation
func NegationR(sequent Sequent) Sequent {
	formulaIndex := len(sequent.Right) - 1
	if formulaIndex < len(sequent.Right) {
		formula := sequent.Right[formulaIndex]
		if strings.HasPrefix(formula.Content, "¬") {
			// Move negated formula to left and remove negation
			// newLeft := append(sequent.Left, Formula{Content: strings.TrimPrefix(formula.Content, "¬")})
			t := strings.TrimPrefix(formula.Content, "¬")
			tt := Formula{Content: t}
			newLeft := append([]Formula{tt}, sequent.Left...)

			// Remove the original formula from right
			// newRight := append(sequent.Right[:formulaIndex], sequent.Right[formulaIndex+1:]...)
			newRight := sequent.Right[:len(sequent.Right)-1]

			newSequent := Sequent{
				Left:  newLeft,
				Right: newRight,
			}
			return newSequent
		}
	}
	return sequent
}

// Implication Right (⊃R) Rule 常に右端
func ImplicationR(sequent Sequent) Sequent {
	formulaIndex := len(sequent.Right) - 1
	if formulaIndex < len(sequent.Right) {
		formula := sequent.Right[formulaIndex]

		// Check if the formula is an implication
		if strings.Contains(formula.Content, "⊃") {
			parts := strings.Split(formula.Content, "⊃")
			phi := parts[0]
			psi := parts[1]

			phi = strings.TrimSpace(phi)
			psi = strings.TrimSpace(psi)
			tt := Formula{Content: phi}
			newLeft := append([]Formula{tt}, sequent.Left...)
			newRight := sequent.Right[:len(sequent.Right)-1]
			newRight = append(newRight, Formula{psi})

			newSequent := Sequent{
				Left:  newLeft,
				Right: newRight,
			}
			return newSequent
		}
	}

	return sequent
}

// Reverse Disjunction Right 1 (Reverse ∨R1) Rule
func ReverseDisjunctionR1(sequent Sequent) Sequent {
	formulaIndex := len(sequent.Right) - 1
	if formulaIndex < len(sequent.Right) {
		parts := strings.Split(sequent.Right[formulaIndex].Content, " ∨ ")
		if len(parts) > 1 {
			// Keep only the first part of the disjunction
			sequent.Right[formulaIndex] = Formula{Content: strings.TrimSpace(parts[0])}
		}
	}

	return sequent
}

// Reverse Disjunction Right 2 (Reverse ∨R2) Rule
func ReverseDisjunctionR2(sequent Sequent) Sequent {
	formulaIndex := len(sequent.Right) - 1
	if formulaIndex < len(sequent.Right) {
		parts := strings.Split(sequent.Right[formulaIndex].Content, " ∨ ")
		if len(parts) > 1 {
			// Keep only the second part of the disjunction
			sequent.Right[formulaIndex] = Formula{Content: strings.TrimSpace(parts[1])}
		}
	}

	return sequent
}

// Conjunction Left 1 (∧L1) Rule
func ConjunctionL1(sequent Sequent) Sequent {
	formulaIndex := 0
	if formulaIndex < len(sequent.Left) {
		parts := strings.Split(sequent.Left[formulaIndex].Content, " ∧ ")
		if len(parts) > 1 {
			// Replace the conjunction with the first part
			sequent.Left[formulaIndex] = Formula{Content: parts[0]}
		}
	}

	return sequent
}

// Conjunction Left 2 (∧L2) Rule
func ConjunctionL2(sequent Sequent) Sequent {
	formulaIndex := 0
	if formulaIndex < len(sequent.Left) {
		parts := strings.Split(sequent.Left[formulaIndex].Content, " ∧ ")
		if len(parts) > 1 {
			// Replace the conjunction with the second part
			sequent.Left[formulaIndex] = Formula{Content: parts[1]}
		}
	}

	return sequent
}

var limit int
func applyRule(sequent Sequent, md int) (Sequent,bool) {
	md += 1
	//fmt.Println(md)
	if md >  limit {
		return sequent, false
	}


	r := Sequent{}
	pok := false
	for i := 0; i < 12; i++ {
		sequent:=sequent
		switch i {
		case 0:
			r = ReverseWeakeningL(sequent)
	//fmt.Println("ReverseWeakeningL")
		case 1:
			r = ReverseWeakeningR(sequent)
	//fmt.Println("ReverseWeakeningR")
		case 2:
			r = ReverseContractionR(sequent)
	//fmt.Println("ReverseContractionR")
		case 3:
			r = ReverseContractionL(sequent)
	//fmt.Println("ReverseContractionL")
		case 4:
			r = ReverseExchangeL(sequent, 0, 1)
	//fmt.Println("ReverseExchangeL")
		case 5:
			r = ReverseExchangeR(sequent, 0, 1)
	//fmt.Println("ReverseExchangeR")
		case 6:
			r = NegationL(sequent)
	//fmt.Println("NegationL")
		case 7:
			r = ImplicationR(sequent)
	//fmt.Println("ImplicationR")
		case 8:
			r = NegationR(sequent)
	//fmt.Println("NegationR")
		case 9:
			r = ReverseDisjunctionR1(sequent)
	//fmt.Println("ReverseDisjunctionR1")
		case 10:
			r = ReverseDisjunctionR2(sequent)
	//fmt.Println("ReverseDisjunctionR2")
		case 11:
			r = ConjunctionL1(sequent)
	//fmt.Println("ConjunctionL1")
		case 12:
			r = ConjunctionL2(sequent)
	//fmt.Println("ConjunctionL2")
		}

		if len(r.Left) == 0 && len(r.Right) == 0 {
			continue
		}
		if len(r.Left) >= 1 && reflect.DeepEqual(r.Left, r.Right) {
			return r, true
		}
	r,pok := applyRule(r, md)
		if pok {
			return r,pok
		}
	}

	return r,pok

}
func prove(sequent Sequent) bool {
	if len(sequent.Left) > 0 && reflect.DeepEqual(sequent.Left, sequent.Right) {
		return true
	}

	s,_ := applyRule(sequent, 100)
	if len(s.Left) < 0 || len(s.Right) < 0 {
		return false
	}
	if !prove(s) {
		return false
	}
	return true
}

func main() {
	limit = 20

	{
		gamma := []Formula{}
		delta := []Formula{{Content: "A ⊃  B ∨  B ⊃  A"}}

		sequent := Sequent{Left: gamma, Right: delta}

		s,ok := applyRule(sequent,0)
		if ok {

			fmt.Println("ok")
			fmt.Println(s)
		} else {
			fmt.Println("no")
		}
	}
	{
		gamma := []Formula{}
		delta := []Formula{{Content: "A ⊃  B ∨  B ⊃  A"}}

		sequent := Sequent{Left: gamma, Right: delta}

		//contR
		t := ReverseContractionR(sequent)
		//fmt.Println(t)
		// R1
		t = ReverseDisjunctionR1(t)
		//fmt.Println(t)

		t = ReverseExchangeR(t, 0, 1)
		//fmt.Println(t)

		t = ReverseDisjunctionR2(t)
		//fmt.Println(t)

		t = ImplicationR(t)
		//fmt.Println(t)

		t = ReverseExchangeR(t, 0, 1)
		//fmt.Println(t)

		t = ImplicationR(t)
		//fmt.Println(t)

		t = ReverseExchangeL(t, 0, 1)
		//fmt.Println(t)

		t = ReverseWeakeningL(t)
		//fmt.Println(t)

		t = ReverseWeakeningR(t)
		//fmt.Println(t)

	}
	// ⊃

	return
	/*
	   // Example usage
	   gamma := []Formula{{Content: "A"}, {Content: "B"}}
	   delta := []Formula{{Content: "C"}}

	   sequent := Sequent{Left: gamma, Right: delta}

	   // Apply Reverse Weakening Left
	   reversedWeakenedSequent := ReverseWeakeningL(sequent, 0) // Remove "B"

	   // Apply Reverse Contraction Right
	   reversedContractedSequent := ReverseContractionR(sequent, 0) // Duplicate "C"

	   fmt.Println("Original Sequent:", sequent)
	   fmt.Println("After Reverse Weakening Left:", reversedWeakenedSequent)
	   fmt.Println("After Reverse Contraction Right:", reversedContractedSequent)
	*/

	gamma := []Formula{{Content: "A"} /*, {Content: "B"}, {Content: "E"}, {Content: "F"}*/}
	delta := []Formula{{Content: "C"}, {Content: "D"}}

	sequent := Sequent{Left: gamma, Right: delta}
	fmt.Println("Original Sequent:", sequent)

	// Apply Reverse Weakening Left
	reversedWeakenedSequentL := ReverseWeakeningL(sequent) // Remove "B" from Left

	// Apply Reverse Contraction Right
	reversedContractedSequentR := ReverseContractionR(sequent) // Duplicate "C" in Right

	// Apply Reverse Weakening Right
	reversedWeakenedSequentR := ReverseWeakeningR(sequent) // Remove "D" from Right

	// Apply Reverse Contraction Left
	reversedContractedSequentL := ReverseContractionL(sequent) // Duplicate "E" in Left

	// Apply Reverse Exchange Left
	reversedExchangedSequentL := ReverseExchangeL(sequent, 0, 1) // Swap "A" and "E" in Left

	fmt.Println("After Reverse Weakening Left:", reversedWeakenedSequentL)
	fmt.Println("After Reverse Contraction Right:", reversedContractedSequentR)
	fmt.Println("After Reverse Weakening Right:", reversedWeakenedSequentR)
	fmt.Println("After Reverse Contraction Left:", reversedContractedSequentL)
	fmt.Println("After Reverse Exchange Left:", reversedExchangedSequentL)

	gamma = []Formula{{Content: "A"} /*, {Content: "B"}, {Content: "E"}, {Content: "F"}*/}
	delta = []Formula{{Content: "C"}, {Content: "D"}}

	sequent = Sequent{Left: gamma, Right: delta}
	// Apply Reverse Exchange Right
	reversedExchangedSequentR := ReverseExchangeR(sequent, 0, 1) // Swap "C" and "D" in Right
	fmt.Println("After Reverse Exchange Right:", reversedExchangedSequentR)

	{

		gamma := []Formula{{Content: "A"}, {Content: "B"}}
		delta := []Formula{{Content: "E"}, {Content: "C ⊃ D"}}

		sequent := Sequent{Left: gamma, Right: delta}
		fmt.Println("Original Sequent:", sequent)

		// Apply Implication Right (⊃R) to the formula "C ⊃ D" in Right
		implicationRSequent := ImplicationR(sequent) // Adds "C" to Left and replaces "C ⊃ D" with "D" in Right

		fmt.Println("After Applying Implication Right (⊃R):", implicationRSequent)

	}

	{
		gamma := []Formula{{Content: "A"}, {Content: "B"}}
		delta := []Formula{{Content: "C ∨ D"}, {Content: "E ∨ F"}}

		sequent := Sequent{Left: gamma, Right: delta}
		fmt.Println("Original Sequent:", sequent)

		// Apply Reverse Disjunction Right 1 (Reverse ∨R1)
		//	reverseDisjunctionR1Sequent := ReverseDisjunctionR1(sequent) // Keeps "C" from "C ∨ D"

		// Apply Reverse Disjunction Right 2 (Reverse ∨R2)
		reverseDisjunctionR2Sequent := ReverseDisjunctionR2(sequent) // Keeps "F" from "E ∨ F"

		//	fmt.Println("After Applying Reverse Disjunction Right 1 (Reverse ∨R1):", reverseDisjunctionR1Sequent)
		fmt.Println("After Applying Reverse Disjunction Right 2 (Reverse ∨R2):", reverseDisjunctionR2Sequent)
	}

	{
		gamma := []Formula{{Content: "A ∧ B"}, {Content: "C ∧ D"}}
		delta := []Formula{{Content: "E"}, {Content: "F"}}

		sequent := Sequent{Left: gamma, Right: delta}
		fmt.Println("Original Sequent:", sequent)

		// Apply Conjunction Left 1 (∧L1)
		//conjunctionL1Sequent := ConjunctionL1(sequent) // Keeps "A" from "A ∧ B"

		// Apply Conjunction Left 2 (∧L2)
		conjunctionL2Sequent := ConjunctionL2(sequent) // Keeps "D" from "C ∧ D"

		//fmt.Println("After Applying Conjunction Left 1 (∧L1):", conjunctionL1Sequent)
		fmt.Println("After Applying Conjunction Left 2 (∧L2):", conjunctionL2Sequent)
	}

}
