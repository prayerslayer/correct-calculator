import React from 'react';
import Calculator from './Calculator';
import styled from 'styled-components';

const Paragraph = styled.p`
  max-width: 600px;
  margin: 0 auto;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif, "Apple Color Emoji", "Segoe UI Emoji", "Segoe UI Symbol";
`;

const Spacer = styled.div`margin-bottom: 100px;`;

const Headline = styled.h1`
  text-align: center;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif, "Apple Color Emoji", "Segoe UI Emoji", "Segoe UI Symbol";
`;

export default function App() {
  return (
    <main>
      <Headline>Correct Calculator</Headline>
      <Paragraph>
        Works on natural numbers. Correctness of functions verified by Coq,
        transpiled to Javascript via OCaml (Bucklescript).
      </Paragraph>
      <Spacer />
      <Calculator />
    </main>
  );
}
