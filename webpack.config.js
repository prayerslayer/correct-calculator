var path = require('path');
var webpack = require('webpack');
var HtmlWebpackPlugin = require('html-webpack-plugin');
const MinifyPlugin = require("babel-minify-webpack-plugin");

const PROD = process.env.NODE_ENV === 'production'

const defaultPlugins = [
  new HtmlWebpackPlugin(),
  new webpack.NamedModulesPlugin(),
  new webpack.HotModuleReplacementPlugin(),
  new webpack.EnvironmentPlugin({
    NODE_ENV: 'dev'
  })
]

const prodPlugins = PROD ?  [
  new MinifyPlugin()
] : []

module.exports = {
  context: __dirname,

  entry: [
    "react-hot-loader/patch",
    path.resolve(__dirname, './src')
  ],

  output: {
    path: path.resolve(__dirname, './docs/'),
    filename: '[name]-[hash].js'
  },

  plugins: [...defaultPlugins, ...prodPlugins],

  devServer: {
    contentBase: path.resolve(__dirname, './docs/'),
    hot: true
  },

  module: {
    rules: [
      {
        test: /\.jsx?$/,
        exclude: /node_modules/,
        use: 'babel-loader'
      },
      {
        test: /\.(jpg|png|gif|eot|svg|ttf|woff|woff2)(\?.*)?$/,
        use: 'file-loader'
      }
    ]
  },

  resolve: {
    extensions: ['.js', '.jsx']
  }
};
