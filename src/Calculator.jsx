import React from 'react';
import { add, sub, mult, div } from '../lib/math';
import styled from 'styled-components';

const fontFamily =
  '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif, "Apple Color Emoji", "Segoe UI Emoji", "Segoe UI Symbol"';
const Button = styled.button`
  font-family: ${fontFamily};
  font-weight: 300;
  font-size: 24px;
  min-height: 70px;
  min-width: 70px;
  background: #eee;
  border: none;

  &:hover,
  &:focus {
    cursor: pointer;
    z-index: 1;
    outline: none;
    box-shadow: 0 0 20px 1px rgba(0, 0, 0, 0.1);
  }
`;

const OperatorButton = Button.extend`
  background: orange;
  color: white;
  font-size: 30px;
`;

const Display = styled.div`
  font-family: ${fontFamily};
  font-weight: 300;
  text-align: right;
  background: #aaa;
  color: white;
  padding: 5px 18px;
  font-size: 60px;
  grid-area: display;

  &::selection {
    background: #aaa;
    color: white;
  }
`;

const SpecialGrid = styled.div`
  display: grid;
  grid-template-columns: auto;
  grid-area: special;
`;

const NumpadGrid = styled.div`
  display: grid;
  grid-template-columns: repeat(3, auto);
  grid-template-rows: repeat(4, auto);
  grid-area: numpad;

  > :last-child {
    grid-column: 1/3;
    grid-column-end: span 3;
  }
`;

const OperatorGrid = styled.div`
  display: grid;
  grid-template-rows: repeat(5, auto);
  grid-template-columns: auto;
  grid-area: operators;
  align-self: start;
  grid-auto-flow: column;
`;

const CalculatorGrid = styled.div`
  display: grid;
  grid-template-columns: auto auto;
  grid-template-rows: auto auto auto;
  justify-content: center;

  grid-template-areas: 'display display' 'special operators' 'numpad operators';
`;

function noop() {}

function formatNumber(nr) {
  return Intl.NumberFormat().format(nr);
}

function Numpad({ children, onClick = noop }) {
  return [7, 8, 9, 4, 5, 6, 1, 2, 3, 0].map(i => (
    <Button onClick={() => onClick(i)} key={i}>
      {i}
    </Button>
  ));
}

const ops = [['\u00f7', div], ['\u00d7', mult], ['-', sub], ['+', add]];
function Operators({ onClick = noop }) {
  return ops.map(([label, op]) => (
    <OperatorButton onClick={() => onClick(op)} key={label}>
      {label}
    </OperatorButton>
  ));
}

const INITIAL_STATE = {
  pendingOperation: null,
  value: 0
};
export default class Calculator extends React.Component {
  constructor(p) {
    super(p);
    this.state = INITIAL_STATE;
  }

  clear = () => this.setState(INITIAL_STATE);

  updateValue = val =>
    this.setState(state => ({
      value: state.value * 10 + val
    }));

  prepareOperation = op =>
    this.setState(state => ({
      pendingOperation: op.bind(
        null,
        state.pendingOperation !== null
          ? state.pendingOperation(state.value)
          : state.value
      ),
      value: 0
    }));

  calculate = () =>
    this.setState(state => ({
      value: this.state.pendingOperation(state.value),
      pendingOperation: null
    }));

  render() {
    return (
      <CalculatorGrid>
        <Display>{formatNumber(this.state.value)}</Display>
        <SpecialGrid>
          <Button onClick={this.clear}>AC</Button>
        </SpecialGrid>
        <NumpadGrid>
          <Numpad onClick={this.updateValue} />
        </NumpadGrid>
        <OperatorGrid>
          <Operators onClick={this.prepareOperation} />
          <OperatorButton onClick={this.calculate}>=</OperatorButton>
        </OperatorGrid>
      </CalculatorGrid>
    );
  }
}