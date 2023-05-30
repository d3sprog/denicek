module.exports = {
  moduleFileExtensions: ['js'],
  roots: ['./output'],
  testMatch: ['<rootDir>/**/tests.js'],
  coveragePathIgnorePatterns: ['/\.fable/', '/[fF]able.*/', '/node_modules/'],
  testEnvironment: 'node',
  transform: {}
};