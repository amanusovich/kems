package logic.labelledFormulas;

import java.util.Objects;

import util.NotImplementedException;

public class FormulaLabel implements Comparable<FormulaLabel>{
	public enum LabelType {
		CONSTANT, VARIABLE, NONE
	}

	protected final LabelType type;
	private final int index;

	public FormulaLabel(LabelType type, int index) {
		this.type = type;
		this.index = index;
	}

	public static FormulaLabel constant(int index) {
		return new FormulaLabel(LabelType.CONSTANT, index);
	}

	public static FormulaLabel variable(int index) {
		return new FormulaLabel(LabelType.VARIABLE, index);
	}

	public static FormulaLabel empty() {
		return new FormulaLabel(LabelType.NONE, 0);
	}

	public boolean isConstant() {
		return this.type == LabelType.CONSTANT;
	}

	public boolean isVariable() {
		return this.type == LabelType.VARIABLE;
	}

	public int getIndex() {
		return this.index;
	}

	public boolean isEmpty() {
		return this.type == LabelType.NONE;
	}
	
	public FormulaLabel getNextFormulaLabel() {
		
		return new FormulaLabel(LabelType.CONSTANT, this.index + 1);
	}

	@Override
	public String toString() {
		if (isEmpty()) return "";
		return (isConstant() ? "c" : "x") + this.index;
	}

	@Override
	public int compareTo(FormulaLabel o) {
		return this.index - o.getIndex();
	}

	@Override
	public int hashCode() {
		return Objects.hash(index, type);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FormulaLabel other = (FormulaLabel) obj;
		return index == other.index && type == other.type;
	}

	public boolean lowerOrEqualThan(FormulaLabel aux) {
		boolean result = this.index <= aux.getIndex();
		// System.out.println("DEBUG: FormulaLabel.lowerOrEqualThan - this: " + this + " (index=" + this.index + "), aux: " + aux + " (index=" + aux.getIndex() + "), result: " + result);
		return result;
	}
	public boolean lowerThan(FormulaLabel aux) {
		return this.index < aux.getIndex();
	}

    public FormulaLabel getGreaterFormulaLabel() {
		// For IPL: create a new label with a higher index
		return new FormulaLabel(this.type, this.index + 1);
    }

	public FormulaLabel getLowerFormulaLabel() {
		// For IPL: create a new label with a lower index (if possible)
		if (this.index > 0) {
			return new FormulaLabel(this.type, this.index - 1);
		} else {
			// Already at index 0, return a new c0 label
			return new FormulaLabel(this.type, 0);
		}
	}
}