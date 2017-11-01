import React from 'react';
import {
  add,
  sub,
  mult,
  div,
  zero,
  one,
  two,
  three,
  four,
  five,
  six,
  seven,
  eight,
  nine,
  ten
} from '../lib/math';
import styled, { keyframes } from 'styled-components';

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
  margin: 0;
  padding: 0;

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

const evalAnim = keyframes`
from {
  opacity: 0;
}

to {
  opacity: 1;
}
`;

const DisplayNumber = styled.div`
  font-family: ${fontFamily};
  font-weight: 300;
  color: white;
  font-size: 60px;

  &::selection {
    background: #aaa;
    color: white;
  }
`;

const AnimatedDisplayNumber = DisplayNumber.extend`
  animation-name: ${evalAnim};
  animation-duration: 0.2s;
  animation-timing-function: ease-in-out;
  animation-delay: 0s;
  animation-iteration-count: 1;
`;

const Display = styled.div`
  text-align: right;
  background: #aaa;
  padding: 5px 18px;
  grid-area: display;
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

const nums = [seven, eight, nine, four, five, six, one, two, three, zero];
function Numpad({ children, onClick = noop }) {
  return nums.map(i => (
    <Button onClick={() => onClick(i)} key={i}>
      {i}
    </Button>
  ));
}

const ops = [
  ['\u00f7', div],
  ['\u00d7', mult],
  ['\u2212', sub],
  ['\u002B', add]
];
function Operators({ onClick = noop }) {
  return ops.map(([label, op]) => (
    <OperatorButton onClick={() => onClick(op)} key={label}>
      {label}
    </OperatorButton>
  ));
}

const INITIAL_STATE = {
  pendingOperation: null,
  value: zero,
  evaled: false
};
export default class Calculator extends React.Component {
  constructor(p) {
    super(p);
    this.state = INITIAL_STATE;
  }

  clear = () => this.setState(INITIAL_STATE);

  hasPendingOperation = state => state.pendingOperation !== null;

  updateValue = val =>
    this.setState(state => ({
      value: add(mult(state.value, ten), val),
      evaled: false
    }));

  prepareOperation = op =>
    this.setState(state => ({
      evaled: false,
      pendingOperation: op.bind(
        null,
        this.hasPendingOperation(state)
          ? state.pendingOperation(state.value)
          : state.value
      ),
      value: zero
    }));

  evaluate = () =>
    this.setState(
      state =>
        this.hasPendingOperation(state)
          ? {
              value: state.pendingOperation(state.value),
              pendingOperation: null,
              evaled: true
            }
          : state
    );

  render() {
    const NumberComp = this.state.evaled
      ? AnimatedDisplayNumber
      : DisplayNumber;
    return (
      <CalculatorGrid>
        <Display>
          <NumberComp>{formatNumber(this.state.value)}</NumberComp>
        </Display>
        <SpecialGrid>
          <Button onClick={this.clear}>C</Button>
        </SpecialGrid>
        <NumpadGrid>
          <Numpad onClick={this.updateValue} />
        </NumpadGrid>
        <OperatorGrid>
          <Operators onClick={this.prepareOperation} />
          <OperatorButton onClick={this.evaluate}>=</OperatorButton>
        </OperatorGrid>
      </CalculatorGrid>
    );
  }
}
