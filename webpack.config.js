var path = require('path');
var webpack = require('webpack');
var HtmlWebpackPlugin = require('html-webpack-plugin');
module.exports = {
  context: __dirname,

  entry: [
    "react-hot-loader/patch",
    path.resolve(__dirname, './src')
  ],

  output: {
    path: path.resolve(__dirname, './dist/'),
    filename: '[name]-[hash].js'
  },

  plugins: [
    new HtmlWebpackPlugin(),
    new webpack.NamedModulesPlugin(),
    new webpack.HotModuleReplacementPlugin()
  ],

  devServer: {
    contentBase: path.resolve(__dirname, './dist/'),
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
