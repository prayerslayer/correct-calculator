import App from './App'
import React from 'react';
import DOM from 'react-dom'

function render(Component) {
  DOM.render( <Component />, document.querySelector("body"))
}

window.addEventListener("DOMContentLoaded", () => render(App))

if (module.hot) {
  module.hot.accept('./App', function(Comp) {
    render(Comp);
  });
}
