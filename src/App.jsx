import React from 'react';
import Calculator from './Calculator';
import styled from 'styled-components';

const Paragraph = styled.p`
  max-width: 600px;
  margin: 0 auto;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Helvetica,
    Arial, sans-serif, 'Apple Color Emoji', 'Segoe UI Emoji', 'Segoe UI Symbol';
`;

const Danger = Paragraph.extend`
  background: red;
  color: white;
`;

const Spacer = styled.div`margin-bottom: 70px;`;

const Headline = styled.h1`
  text-align: center;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Helvetica,
    Arial, sans-serif, 'Apple Color Emoji', 'Segoe UI Emoji', 'Segoe UI Symbol';
`;

export default class App extends React.Component {
  constructor(p) {
    super(p);
    this.state = {
      error: null
    };
  }
  componentDidCatch(e) {
    this.setState({ error: e });
  }
  render() {
    if (this.state.error !== null) {
      return <Danger>Error: {this.state.error.message}</Danger>
    }
    return (
      <main>
        <Headline>Correct Calculator</Headline>
        <Paragraph>
          Works on natural numbers. Correctness of functions verified by Coq,
          transpiled to Javascript via OCaml (Bucklescript).{' '}
          <a href="https://github.com/prayerslayer/correct-calculator">
            Github
          </a>
        </Paragraph>
        <Spacer />
        <Calculator />
      </main>
    );
  }
}
