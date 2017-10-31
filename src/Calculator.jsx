import React from 'react';
import { add, sub, mult, div } from '../lib/math';

function range(n) {
  return new Array(n).fill(0).map((_, i) => i);
}

function noop() {}

function Numpad({ onClick = noop }) {
  return range(10).map(i => (
    <button onClick={() => onClick(i)} key={i}>
      {i}
    </button>
  ));
}

function Operators({ onClick = noop }) {
  return [
    ['+', add],
    ['-', sub],
    ['x', mult],
    ['/', div]
  ].map(([label, op]) => (
    <button onClick={() => onClick(op)} key={label}>
      {label}
    </button>
  ));
}

function Display({ value = 0 }) {
  return <div>{value}</div>;
}

const INITIAL_STATE = {
  pendingOperation: null,
  value: 0,
  decimalPlace: 0
};
export default class Calculator extends React.Component {
  constructor(p) {
    super(p);
    this.state = INITIAL_STATE;
  }

  clear = () => this.setState(INITIAL_STATE);

  updateValue = val =>
    this.setState(state => ({
      value: state.value * 10 + val,
      decimalPlace: state.decimalPlace + 1
    }));

  prepareOperation = op =>
    this.setState(state => ({
      pendingOperation: op.bind(
        null,
        state.pendingOperation !== null
          ? state.pendingOperation(state.value)
          : state.value
      ),
      decimalPlace: 0,
      value: 0
    }));

  calculate = () =>
    this.setState(state => ({
      value: this.state.pendingOperation(state.value),
      pendingOperation: null,
      decimalPlace: 0
    }));

  render() {
    return (
      <div>
        <Display value={this.state.value} />
        <Numpad onClick={this.updateValue} />
        <Operators onClick={this.prepareOperation} />
        <button onClick={this.calculate}>=</button>
        <button onClick={this.clear}>AC</button>
      </div>
    );
  }
}
